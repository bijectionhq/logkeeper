"""Parse the linked Verus fragment and elaborate it to Lean.

The lexer retains source locations and the parser consumes whole definitions.
The emitter accepts only the operations and representation mappings below.
"""

from dataclasses import dataclass
import re


class Unsupported(ValueError):
    pass


LEX = re.compile(
    r'//[^\n]*|/\*.*?\*/|"(?:[^"\\]|\\.)*"|\s+|[A-Za-z_][A-Za-z_0-9]*|[0-9][0-9_]*'
    r'|<==>|==>|=~=|&&&|\|\|\||::|->|=>|==|!=|<=|>=|&&|\|\||\S',
    re.S,
)


@dataclass(frozen=True)
class Token:
    word: str
    line: int


def lex(source):
    result = []
    line = 1
    for match in LEX.finditer(source):
        token = match[0]
        if not (token.isspace() or token.startswith(("//", "/*"))):
            result.append(Token(token, line))
        line += token.count("\n")
    return result


@dataclass(frozen=True)
class Type:
    name: str
    args: tuple = ()


def ty(name, *args):
    return Type(name, args)


UNIT = ty("unit")
PROP = ty("prop")
BOOL = ty("bool")
INT = ty("int")
NAT = ty("nat")
USIZE = ty("usize")
U64 = ty("u64")
BYTE = ty("u8")
NUMBER = ty("numeral")


@dataclass
class Definition:
    name: str
    generics: tuple
    inputs: dict
    ordered: tuple
    output: Type
    body: tuple
    decreases: str | None
    line: int


# Rust precedence, with word operators used by Verus.
INFIX = {
    "==>": 1, "implies": 1, "<==>": 1,
    "||": 2, "&&": 3, "==": 4, "!=": 4, "=~=": 4,
    "<": 5, "<=": 5, ">": 5, ">=": 5,
    "+": 6, "-": 6, "*": 7, "as": 8,
}
ORDER = {"<", "<=", ">", ">="}


class Parser:
    def __init__(self, tokens, path):
        self.tokens = tokens + [Token("<eof>", tokens[-1].line if tokens else 1)]
        self.path = path
        self.pos = 0

    def fail(self, message):
        raise Unsupported(f"{self.path}:{self.tokens[self.pos].line}: {message}")

    def peek(self):
        return self.tokens[self.pos].word

    def take(self):
        word = self.peek()
        if word == "<eof>":
            self.fail("unexpected end of file")
        self.pos += 1
        return word

    def accept(self, word):
        if self.peek() == word:
            self.take()
            return True
        return False

    def need(self, word):
        if not self.accept(word):
            self.fail(f"expected {word!r}, found {self.peek()!r}")

    def identifier(self):
        word = self.take()
        if not re.fullmatch(r"[A-Za-z_]\w*", word):
            self.fail(f"expected identifier, found {word!r}")
        return word

    def separated(self, read, end):
        values = []
        while not self.accept(end):
            values.append(read())
            if not self.accept(","):
                self.need(end)
                break
        return tuple(values)

    def type(self):
        if self.accept("&"):
            # The shared reference observes the value, without a Rust lifetime.
            return self.type()
        if self.accept("("):
            args = self.separated(self.type, ")")
            return ty("tuple", *args) if args else UNIT
        if self.accept("["):
            item = self.type()
            self.need(";")
            width = self.take()
            if not width.isascii() or not width.isdecimal():
                self.fail(f"unsupported array width {width!r}")
            self.need("]")
            return ty("Array", item, ty(width))
        if self.accept("spec_fn"):
            self.need("(")
            args = self.separated(self.type, ")")
            self.need("->")
            return ty("function", *args, self.type())
        name = self.identifier()
        if name == "Fingerprint":
            return ty("Array", BYTE, ty("32"))
        if name == "BallotRank":
            return ty("tuple", U64, ty("u128"))
        if name in INTEGER or name == "bool":
            return ty(name)
        return ty(name, *self.separated(self.type, ">")) if self.accept("<") else ty(name)

    def binder(self):
        name = self.identifier()
        self.need(":")
        return name, self.type()

    def path_name(self):
        path = self.identifier()
        while self.accept("::"):
            path += "::" + self.identifier()
        return path

    def pattern(self):
        if self.accept("("):
            return ("tuple", self.separated(self.pattern, ")"))
        if self.peek().isdigit() or self.peek() in ("true", "false"):
            return ("literal", self.take())
        name = self.path_name()
        if self.accept("("):
            return ("constructor", name, self.separated(self.pattern, ")"))
        if name == "None" or "::" in name:
            return ("constructor", name, ())
        return ("binder", name)

    def trigger(self):
        # Solver-only annotation. Reject arbitrary attributes.
        while self.accept("#"):
            inner = self.accept("!")
            self.need("[")
            self.need("trigger")
            if inner:
                self.separated(self.expr, "]")
            else:
                self.need("]")

    def block(self):
        self.need("{")
        if self.accept("let"):
            name = self.identifier()
            self.need("=")
            value = self.expr()
            self.need(";")
            return ("let", name, value, self.block_contents())
        result = self.expr()
        self.need("}")
        return result

    def block_contents(self):
        if self.accept("let"):
            name = self.identifier()
            self.need("=")
            value = self.expr()
            self.need(";")
            return ("let", name, value, self.block_contents())
        result = self.expr()
        self.need("}")
        return result

    def prefix(self):
        self.trigger()
        if self.peek() == "{":
            return self.block()
        if self.accept("if"):
            cond = self.expr()
            yes = self.block()
            self.need("else")
            no = self.prefix() if self.peek() == "if" else self.block()
            return ("if", cond, yes, no)
        if self.accept("match"):
            value = self.expr()
            self.need("{")

            def arm():
                pattern = self.pattern()
                guard = self.expr() if self.accept("if") else None
                self.need("=>")
                result = self.block() if self.peek() == "{" else self.expr()
                return pattern, guard, result

            return ("match", value, self.separated(arm, "}"))
        if self.peek() in ("forall", "exists", "|"):
            quantifier = "lambda" if self.peek() == "|" else self.take()
            self.need("|")
            binders = self.separated(self.binder, "|")
            return ("quantifier", quantifier, binders, self.expr())
        if self.peek() in ("!", "-", "*", "&"):
            return ("unary", self.take(), self.expr(9))
        if self.peek() in ("&&&", "|||"):
            separator = self.take()
            values = [self.expr()]
            while self.accept(separator):
                values.append(self.expr())
            return ("boolean_list", separator, tuple(values))
        if self.accept("("):
            if self.accept(")"):
                return ("tuple", ())
            first = self.expr()
            if self.accept(")"):
                return first
            self.need(",")
            if self.peek() == ")":
                self.fail("one-element tuples are unsupported")
            return ("tuple", (first, *self.separated(self.expr, ")")))
        if re.fullmatch(r"[0-9][0-9_]*", self.peek()):
            value = self.take().replace("_", "")
            suffix = self.take() if self.peek() in ("u8", "u32", "u64", "usize", "int", "nat") else None
            return ("literal", value, suffix)
        name = self.path_name()
        if name == "seq" and self.accept("!"):
            self.need("[")
            return ("list", self.separated(self.expr, "]"))
        return ("name", name)

    def expr(self, minimum=0):
        left = self.prefix()
        while True:
            op = self.peek()
            if self.accept("("):
                if left == ("name", "Seq::new"):
                    length = self.expr()
                    self.need(",")
                    self.need("|")
                    index = self.identifier()
                    index_type = self.type() if self.accept(":") else INT
                    self.need("|")
                    body = self.expr()
                    self.accept(",")
                    self.need(")")
                    left = ("seq_new", length, index, index_type, body)
                else:
                    left = ("call", left, self.separated(self.expr, ")"))
            elif self.accept("["):
                index = self.expr()
                self.need("]")
                left = ("index", left, index)
            elif self.accept("."):
                left = ("field", left, self.take())
            elif self.accept("@"):
                left = ("view", left)
            elif minimum <= 4 and (self.accept("is") or self.accept("matches")):
                operator = self.tokens[self.pos - 1].word
                pattern = self.pattern()
                if operator == "is" and pattern[0] == "binder":
                    pattern = ("constructor", pattern[1], None)
                # Explicitly capture Rust's bindings in the right-hand operand.
                following = None
                if operator == "matches" and self.peek() in ("&&", "==>", "implies"):
                    join = self.take()
                    following = (join, self.expr(INFIX[join]))
                left = ("test", left, pattern, following)
            elif op in INFIX and INFIX[op] >= minimum:
                self.take()
                if op == "as":
                    left = ("cast", left, self.type())
                    continue
                right = self.expr(INFIX[op] + (op not in ("==>", "implies")))
                if op in ORDER:
                    comparisons = [(op, left, right)]
                    while self.peek() in ORDER:
                        op = self.take()
                        next_right = self.expr(INFIX[op] + 1)
                        comparisons.append((op, right, next_right))
                        right = next_right
                    left = ("comparisons", tuple(comparisons))
                else:
                    left = ("binary", op, left, right)
            else:
                return left

    def definition(self):
        line = self.tokens[self.pos].line
        self.need("spec")
        self.need("fn")
        name = self.identifier()

        ordered = []

        def generic():
            var = self.identifier()
            if self.accept(":"):
                self.need("Ord")  # Observed through an explicit order mapping.
                ordered.append(var)
            return var

        params = self.separated(generic, ">") if self.accept("<") else ()
        self.need("(")
        inputs = dict(self.separated(self.binder, ")"))
        self.need("->")
        output = self.type()
        measure = None
        if self.accept("decreases"):
            measure = self.identifier()
            if self.accept("."):
                self.need("len")
                self.need("(")
                self.need(")")
                measure += ".length"
            self.need(",")
        return Definition(name, params, inputs, tuple(ordered), output, self.block(), measure, line)


def declarations(source):
    """Index all Rust functions, preserving spec versus executable/proof mode."""
    tokens = lex(source)
    result = {}
    for index, token in enumerate(tokens[:-1]):
        if token.word == "fn" and re.fullmatch(r"[A-Za-z_]\w*", tokens[index + 1].word):
            name = tokens[index + 1].word
            is_spec = index > 0 and tokens[index - 1].word == "spec"
            if name in result:
                raise Unsupported(f"duplicate declaration of {name!r}")
            result[name] = (is_spec, index - is_spec, token.line)
    return tokens, result


def postcondition(tokens, offset, path):
    """Extract the result expression of an executable's Verus contract."""
    signature = Parser(tokens[offset:], path)
    signature.need("fn")
    name = signature.identifier()
    signature.need("(")
    inputs = dict(signature.separated(signature.binder, ")"))
    signature.need("->")
    output = signature.type()

    start = offset - 1
    while start >= 0 and tokens[start].word != "#":
        start -= 1
    contract = Parser(tokens[max(start, 0):offset], path)
    for word in ("#", "[", "cfg_attr", "(", "verus_keep_ghost", ",", "verus_spec", "("):
        contract.need(word)
    result = contract.identifier()
    for word in ("=>", "ensures", result, "=="):
        contract.need(word)
    body = contract.expr()
    contract.accept(",")
    for word in (")", ")", "]", "pub"):
        contract.need(word)
    if contract.accept("("):
        contract.identifier()
        contract.need(")")
    if contract.peek() != "<eof>" or signature.peek() != "{":
        contract.fail("expected one unconditional result postcondition")
    return Definition(name, (), inputs, (), output, body, None, tokens[start].line)


def parenthesize(value):
    return f"({value})"


def ident(name):
    return f"«{name}»"


INTEGER = {"int", "nat", "u8", "u16", "u32", "u64", "u128", "usize", "numeral"}
WIDTH = {"u8": 8, "u16": 16, "u32": 32, "u64": 64, "u128": 128, "usize": 64}


def variant(name):
    return name.split("::")[-1]


class Emitter:
    """Type-directed rendering. Custom type mappings only name Lean types and fields."""

    def __init__(self, definitions, shapes, enums):
        self.definitions = definitions
        self.shapes = shapes
        self.enums = enums

    def type(self, kind, generics):
        name, args = kind.name, kind.args
        if name in ("nat", "u16", "u32", "u64", "u128", "usize", "numeral"):
            return "Nat"
        scalar = {"bool": "Bool", "prop": "Prop", "int": "Int", "u8": "UInt8", "unit": "Unit"}
        if name in scalar:
            return scalar[name]
        if name in generics:
            return ident(name)
        if name == "tuple":
            return parenthesize(" × ".join(self.type(a, generics) for a in args))
        if name == "function":
            return parenthesize(" → ".join(self.type(a, generics) for a in args))
        lean = {"Seq": "List", "Array": "List", "Option": "Option", "Result": "Except",
                "Map": "PartialMap", "Set": "PredSet", "ISet": "PredSet"}.get(name)
        if name == "Result":
            args = args[::-1]
        if name == "Array":
            args = args[:1]
        if name in self.shapes:
            lean = self.shapes[name][0]
        if name in self.enums:
            lean = self.enums[name][0]
        if lean is None:
            raise Unsupported(f"unmapped type {kind}")
        return parenthesize(" ".join((lean, *(self.type(a, generics) for a in args)))) if args else lean

    def infer(self, expr, env):
        """Return None when a constructor/literal needs its contextual type."""
        tag, *p = expr
        if tag == "literal":
            return ty(p[1]) if p[1] else NUMBER
        if tag == "seq_new":
            _, index, index_type, body = p
            element = self.infer(body, env | {index: index_type})
            return ty("Seq", element) if element not in (None, NUMBER) else None
        if tag == "name":
            name = p[0]
            if name in env:
                return env[name]
            if name in ("true", "false"):
                return BOOL
            if name.endswith("::MAX") and name.split("::")[0] in WIDTH:
                return ty(name.split("::")[0])
            if "::" in name and name.split("::")[0] in self.enums:
                return ty(name.split("::")[0])
        if tag == "cast":
            return p[1]
        if tag == "view":
            kind = self.infer(p[0], env)
            return ty("Seq", kind.args[0]) if kind and kind.name == "Array" else kind
        if tag == "field":
            return self.field(self.infer(p[0], env), p[1])[1]
        if tag == "index":
            kind = self.infer(p[0], env)
            if kind and kind.name in ("Map", "Seq", "Array"):
                return kind.args[-1] if kind.name == "Map" else kind.args[0]
        if tag == "call":
            signature, args = self.signature(*p, env)
            if signature:
                return signature[1]
        if tag in ("boolean_list", "comparisons", "test"):
            return PROP
        if tag == "quantifier":
            if p[0] != "lambda":
                return PROP
            return ty("function", *(t for _, t in p[1]), self.infer(p[2], env | dict(p[1])) or PROP)
        if tag == "unary":
            return PROP if p[0] == "!" else self.infer(p[1], env)
        if tag == "binary":
            if p[0] in ("+", "-", "*"):
                left, right = (self.infer(e, env) for e in p[1:])
                if left and left.name == "Seq" and p[0] == "+":
                    return left
                if left and right and {left.name, right.name} <= INTEGER:
                    if p[0] == "-" or INT in (left, right) or {left.name, right.name} & WIDTH.keys():
                        return INT
                    return self.join(left, right)
                return None
            return PROP
        if tag in ("tuple", "list"):
            args = tuple(self.infer(e, env) for e in p[0])
            if tag == "tuple" and all(args):
                return ty("tuple", *args) if args else UNIT
            if tag == "list" and args and args[0]:
                return ty("Seq", args[0])
        if tag == "if":
            return self.join(self.infer(p[1], env), self.infer(p[2], env))
        if tag == "let":
            value = self.infer(p[1], env)
            if value:
                return self.infer(p[2], env | {p[0]: value})
        return None

    @staticmethod
    def join(left, right):
        if left is None or left == NUMBER:
            return right
        if right is None or right == NUMBER or right == left:
            return left
        if left.name == right.name and len(left.args) == len(right.args) and left.args:
            return ty(left.name, *(Emitter.join(a, b) for a, b in zip(left.args, right.args)))
        if left.name in INTEGER and right.name in INTEGER:
            if left == INT or right == INT:
                return INT
            if left == BYTE or right == BYTE:
                raise Unsupported("implicit u8 conversion")
            return NAT
        if left in (PROP, BOOL) and right in (PROP, BOOL):
            return PROP
        raise Unsupported(f"incompatible types {left} and {right}")

    def field(self, kind, name):
        if kind and kind.name == "tuple" and name.isdigit():
            index = int(name)
            if index < len(kind.args):
                path = ".2" * index + (".1" if index < len(kind.args) - 1 else "")
                return path, kind.args[index], None
        if kind and kind.name in self.shapes:
            lean, params, fields = self.shapes[kind.name]
            if name in fields:
                label, result, *adapter = fields[name]
                return "." + label, self.substitute(result, dict(zip(params, kind.args))), next(iter(adapter), None)
        raise Unsupported(f"unmapped field {name!r} on {kind}")

    def substitute(self, kind, substitutions):
        if kind.name in substitutions:
            return substitutions[kind.name]
        return ty(kind.name, *(self.substitute(a, substitutions) for a in kind.args))

    def unify(self, expected, observed, variables, substitutions):
        if observed in (None, NUMBER):
            return
        if expected.name in variables:
            if substitutions.setdefault(expected.name, observed) != observed:
                raise Unsupported(f"incompatible instances of {expected.name}")
        elif expected.name == observed.name:
            for wanted, actual in zip(expected.args, observed.args, strict=True):
                self.unify(wanted, actual, variables, substitutions)

    def signature(self, target, args, env, expected=None):
        if target[0] == "name":
            name = target[1]
            if name in ("Some", "Ok", "Err"):
                if len(args) != 1:
                    raise Unsupported(f"wrong arity for {name}")
                if expected is None and name == "Some" and (element := self.infer(args[0], env)):
                    expected = ty("Option", element)
                kind = "Option" if name == "Some" else "Result"
                if expected and expected.name == kind:
                    return ((expected.args[1 if name == "Err" else 0],), expected), args
                return None, args
            if expected and "::" in name and name.split("::")[0] == expected.name and expected.name in self.enums:
                _, types = self.constructor(name, expected)
                return (types, expected), args
            known = self.definitions.get(name)
            if known:
                types = tuple(known.inputs.values())
                if len(types) != len(args):
                    raise Unsupported(f"wrong arity for {name}")
                substitutions = {}
                for expression, arg in zip(args, types, strict=True):
                    self.unify(arg, self.infer(expression, env), known.generics, substitutions)
                if expected is not None:
                    self.unify(known.output, expected, known.generics, substitutions)
                output = PROP if known.output == BOOL else self.substitute(known.output, substitutions)
                return (tuple(self.substitute(t, substitutions) for t in types), output), args
            if name in env and env[name].name == "function":
                types = env[name].args
                return (types[:-1], types[-1]), args
            if name in ("Set::new", "ISet::new"):
                if len(args) == 1 and (predicate := self.infer(args[0], env)) and predicate.name == "function":
                    return ((ty("function", predicate.args[0], PROP),), ty(name.split("::")[0], predicate.args[0])), args
        if target[0] == "field":
            _, subject, method = target
            kind = self.infer(subject, env)
            if kind is None:
                raise Unsupported(f"unknown receiver type for {method!r}")
            params = kind.args
            methods = {}
            if kind.name in ("Seq", "Array"):
                element = params[0]
                methods = {"len": ((), NAT), "skip": ((INT,), kind), "take": ((INT,), kind),
                           "subrange": ((INT, INT), kind), "drop_first": ((), kind),
                           "contains": ((element,), PROP), "to_set": ((), ty("Set", element))}
            if kind.name == "Map":
                key, value = params
                methods = {"get": ((key,), ty("Option", value)), "contains_key": ((key,), PROP),
                           "values": ((), ty("Set", value))}
            if kind.name in ("Set", "ISet"):
                methods = {"contains": ((params[0],), PROP), "union": ((kind,), kind),
                           "subset_of": ((kind,), PROP)}
            if kind.name == "Option":
                methods = {"is_some": ((), PROP), "is_none": ((), PROP), "unwrap": ((), params[0])}
            if method == "cmp_spec":
                return ((kind, kind), ty("Comparison")), (subject, *args)
            if method in methods:
                types, result = methods[method]
                return ((kind, *types), result), (subject, *args)
        return None, args

    def pattern(self, node, kind, env):
        tag, *p = node
        if kind is None:
            raise Unsupported("cannot infer match scrutinee type")
        if tag == "binder":
            if p[0] != "_":
                env[p[0]] = kind
                return ident(p[0])
            return "_"
        if tag == "tuple" and kind.name == "tuple":
            return "(" + ", ".join(self.pattern(e, t, env) for e, t in zip(p[0], kind.args, strict=True)) + ")"
        if tag == "literal" and (kind.name in INTEGER or kind == BOOL):
            return p[0]
        if tag == "constructor":
            name, args = p
            constructor, types = self.constructor(name, kind)
            args = args if args is not None else (("binder", "_"),) * len(types)
            return " ".join((constructor, *(parenthesize(self.pattern(e, t, env))
                                           for e, t in zip(args, types, strict=True))))
        raise Unsupported(f"unsupported match pattern {node} for {kind}")

    def constructor(self, name, kind):
        name = variant(name)
        if kind.name == "Option" and name in ("Some", "None"):
            return (".some", kind.args) if name == "Some" else (".none", ())
        if kind.name == "Result" and name in ("Ok", "Err"):
            return (".ok", kind.args[:1]) if name == "Ok" else (".error", kind.args[1:])
        if kind.name in self.enums:
            _, params, variants = self.enums[kind.name]
            if name in variants:
                ctor, types = variants[name]
                return ctor, tuple(self.substitute(t, dict(zip(params, kind.args))) for t in types)
        raise Unsupported(f"unmapped constructor {name!r} for {kind}")

    def coerce(self, value, observed, expected):
        if expected is None or observed == expected:
            return value
        if expected == PROP and observed == BOOL:
            return parenthesize(f"{value} = true")
        if expected == BOOL and observed == PROP:
            return parenthesize(f"decide {value}")
        if observed and observed.name in INTEGER and expected.name in INTEGER:
            if expected == INT:
                return parenthesize(f"↑{value + '.toNat' if observed == BYTE else value} : Int")
            if observed not in (INT, BYTE) and expected != BYTE:
                return value
        raise Unsupported(f"unsupported coercion {observed} to {expected}")

    def emit(self, expr, env, expected=None):
        tag, *p = expr
        observed = self.infer(expr, env)
        if tag == "literal":
            output = expected if observed == NUMBER and expected else observed
            spelling = p[0] if p[1] is None else parenthesize(f"{p[0]} : {self.type(output, ())}")
            return self.coerce(spelling, output, expected)
        if tag == "name":
            name = p[0]
            if name in env or name in ("true", "false"):
                return self.coerce(ident(name) if name in env else name, observed, expected)
            if name.endswith("::MAX") and observed and observed.name in WIDTH:
                value = str(2 ** WIDTH[observed.name] - 1)
                return self.coerce(parenthesize(f"{value} : {self.type(observed, ())}"), observed, expected)
            kind = expected or observed
            if kind:
                constructor, args = self.constructor(name, kind)
                if not args:
                    return constructor
        if tag == "view":
            if self.infer(p[0], env) and self.infer(p[0], env).name in ("Array", "Seq", "Map", "Set"):
                return self.emit(p[0], env)
            raise Unsupported(f"unmapped view of {p[0]}")
        if tag == "cast":
            source = self.infer(p[0], env)
            dest = p[1]
            if source is None or source.name not in INTEGER or dest.name not in INTEGER:
                raise Unsupported(f"unsupported cast {source} as {dest}")
            value = self.emit(p[0], env)
            if dest.name in WIDTH and source != dest:
                value = parenthesize(f"clipUnsigned {WIDTH[dest.name]} {self.coerce(value, source, INT)}")
                if dest == BYTE:
                    value = parenthesize(f"UInt8.ofNat {value}")
            elif dest == NAT and source == INT:
                value = parenthesize(f"asNatural {value}")
            elif dest == NAT and source == BYTE:
                value = parenthesize(f"UInt8.toNat {value}")
            else:
                value = self.coerce(value, source, dest)
            return self.coerce(value, dest, expected)
        if tag == "tuple":
            if not p[0]:
                return "()"
            types = expected.args if expected else (None,) * len(p[0])
            return "(" + ", ".join(self.emit(e, env, t) for e, t in zip(p[0], types, strict=True)) + ")"
        if tag == "seq_new":
            length, index, index_type, body = p
            kind = expected or observed
            if kind is None or kind.name != "Seq" or index_type != INT:
                raise Unsupported("Seq::new needs an element type and an int index")
            render_body = self.emit(body, env | {index: INT}, kind.args[0])
            return parenthesize(f"seqNew {self.emit(length, env, NAT)} "
                                f"(fun {ident(index)} => {render_body})")
        if tag == "list":
            kind = expected or observed
            if kind and kind.name == "Seq":
                return "[" + ", ".join(self.emit(e, env, kind.args[0]) for e in p[0]) + "]"
        if tag == "field":
            path, result, adapter = self.field(self.infer(p[0], env), p[1])
            value = parenthesize(self.emit(p[0], env) + path)
            if adapter:
                value = parenthesize(f"{adapter} {value}")
            return self.coerce(value, result, expected)
        if tag == "index":
            base, index = p
            kind = self.infer(base, env)
            if kind and kind.name in ("Array", "Seq", "Map"):
                function = "mapIndex" if kind.name == "Map" else "seqIndex"
                key = kind.args[0] if kind.name == "Map" else INT
                value = parenthesize(f"{function} {self.emit(base, env)} {self.emit(index, env, key)}")
                return self.coerce(value, observed, expected)
        if tag == "call":
            target, arguments = p
            signature, args = self.signature(target, arguments, env, expected)
            if signature:
                types, result = signature
                if target[0] == "name":
                    name = target[1]
                    if name in ("Some", "Ok", "Err"):
                        name = self.constructor(name, result)[0]
                    elif "::" in name and name.split("::")[0] in self.enums:
                        name = self.constructor(name, result)[0]
                    elif name in ("Set::new", "ISet::new"):
                        name = "id"
                    else:
                        name = ident(name)
                else:
                    name = {
                        "len": "List.length", "skip": "seqDrop", "take": "seqTake",
                        "subrange": "seqSubrange", "drop_first": "(List.drop 1)",
                        "contains": {"Seq": "List.Mem", "Array": "List.Mem",
                                     "Set": "setContains", "ISet": "setContains"}[types[0].name]
                        if target[2] == "contains" else "",
                        "to_set": "seqSet", "get": "id", "contains_key": "mapContains",
                        "values": "mapValues", "union": "setUnion", "subset_of": "setSubset",
                        "is_some": "optionSome", "is_none": "optionNone", "unwrap": "optionValue",
                        "cmp_spec": "compare",
                    }[target[2]]
                if len(args) != len(types):
                    raise Unsupported(f"wrong arity for {name}")
                if name == "List.Mem":
                    args, types = args[::-1], types[::-1]
                args_text = [self.emit(e, env, t) for e, t in zip(args, types, strict=True)]
                result_text = parenthesize(" ".join((name, *args_text))) if args else name
                return self.coerce(result_text, result, expected)
        if tag == "unary":
            op, value = p
            if op in ("*", "&"):
                return self.emit(value, env, expected)
            if op == "!":
                return self.coerce(parenthesize("¬ " + self.emit(value, env, PROP)), PROP, expected)
            if op == "-":
                return self.coerce(parenthesize("-" + self.emit(value, env, INT)), INT, expected)
        if tag == "if":
            output = expected or observed
            cond = self.emit(p[0], env, PROP)
            yes, no = (self.emit(e, env, output) for e in p[1:])
            return parenthesize(f"if {cond} then {yes} else {no}")
        if tag == "let":
            name, value, rest = p
            kind = self.infer(value, env)
            if kind is None:
                raise Unsupported(f"cannot infer the type of binding {name}")
            return parenthesize(f"let {ident(name)} := {self.emit(value, env, kind)}; "
                                + self.emit(rest, env | {name: kind}, expected))
        if tag == "match":
            scrutinee, arms = p
            kind = self.infer(scrutinee, env)
            rendered = []
            for pattern, guard, body in arms:
                context = dict(env)
                pat = self.pattern(pattern, kind, context)
                if guard:
                    # Lean match guards are not Rust guards. Keep this exclusion explicit.
                    raise Unsupported("guarded match arm")
                rendered.append(f"| {pat} => {self.emit(body, context, expected)}")
            return "(match " + self.emit(scrutinee, env, kind) + " with\n  " + "\n  ".join(rendered) + ")"
        if tag == "test":
            scrutinee, pattern, following = p
            kind = self.infer(scrutinee, env)
            context = dict(env)
            pat = self.pattern(pattern, kind, context)
            default = "False"
            yes = "True"
            if following:
                join, expression = following
                yes = self.emit(expression, context, PROP)
                default = "True" if join in ("implies", "==>") else "False"
            value = f"(match {self.emit(scrutinee, env, kind)} with | {pat} => {yes} | _ => {default})"
            return self.coerce(value, PROP, expected)
        if tag == "quantifier":
            quantifier, binders, body = p
            if quantifier == "lambda":
                body_type = expected.args[-1]
                prefix = "fun"
                separator = " => "
            else:
                body_type = PROP
                prefix = "∀" if quantifier == "forall" else "∃"
                separator = ", "
            types = self.generics
            params = " ".join(f"({ident(n)} : {self.type(t, types)})" for n, t in binders)
            value = parenthesize(prefix + " " + params + separator + self.emit(body, env | dict(binders), body_type))
            return self.coerce(value, PROP, expected) if quantifier != "lambda" else value
        if tag == "comparisons":
            values = [self.emit(("binary", op, a, b), env, PROP) for op, a, b in p[0]]
            return self.coerce(parenthesize(" ∧ ".join(values)), PROP, expected)
        if tag == "boolean_list":
            op, args = p
            values = [self.emit(x, env, PROP) for x in args]
            return self.coerce(parenthesize((" ∧ " if op == "&&&" else " ∨ ").join(values)), PROP, expected)
        if tag == "binary":
            op, left, right = p
            logical = {"&&": "∧", "||": "∨", "==>": "→", "implies": "→", "<==>": "↔"}
            operators = {"==": "=", "=~=": "=", "!=": "≠", "<=": "≤", ">=": "≥"}
            if op in logical:
                kind = PROP
                result = PROP
            else:
                kind = self.join(self.infer(left, env), self.infer(right, env))
                if op in ("+", "-", "*"):
                    result = observed or expected
                    if result is None:
                        raise Unsupported(f"ambiguous operands of {op}")
                    kind = result
                    if kind.name == "Seq" and op == "+":
                        op = "++"
                else:
                    result = PROP
            if kind in (None, NUMBER):
                raise Unsupported(f"cannot infer operands of {op}")
            # Seq + translates to concatenation, and equality of spec booleans to iff.
            if kind == PROP and op in ("==", "!="):
                value = parenthesize(self.emit(left, env, PROP) + " ↔ " + self.emit(right, env, PROP))
                return self.coerce(value if op == "==" else parenthesize("¬ " + value), PROP, expected)
            value = parenthesize(f"{self.emit(left, env, kind)} "
                                 f"{logical.get(op, operators.get(op, op))} {self.emit(right, env, kind)}")
            return self.coerce(value, result, expected)
        raise Unsupported(f"unsupported expression {expr}")

    def definition(self, definition):
        self.generics = definition.generics
        params = dict(definition.inputs)
        generics = "".join(f" {{{ident(t)} : Type}} [Nonempty {ident(t)}]" for t in definition.generics)
        generics += "".join(f" [Ord {ident(t)}]" for t in definition.ordered)
        args = "".join(f" ({ident(n)} : {self.type(t, self.generics)})" for n, t in params.items())
        result = PROP if definition.output == BOOL else definition.output
        body = self.emit(definition.body, params, result)
        code = f"def {ident(definition.name)}{generics}{args} : {self.type(result, self.generics)} :=\n  {body}\n"
        if definition.decreases:
            parts = definition.decreases.split(".")
            code += "termination_by " + ident(parts[0]) + ("." + parts[1] if len(parts) == 2 else "") + "\n"
            code += "decreasing_by simp_all; first | omega | (unfold asNatural; split <;> omega)\n"
        return code
