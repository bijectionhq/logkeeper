import SharedWAL
import Logkeeper.StreamJournal

namespace Logkeeper.StreamJournal

set_option warningAsError true

/-- A durable stream image whose write was acknowledged survives demultiplexed recovery. -/
theorem replied_stream_image_survives_torn_tail
    (wal : SharedWAL.Log (SharedWAL.Frame Nat (Keeper Payload)))
    (stream : Nat) (row : SharedWAL.Frame Nat (Keeper Payload))
    (tail : List (SharedWAL.Frame Nat (Keeper Payload)))
    (belongs : row.group = stream) (replied : SharedWAL.permitsReply wal row) :
    row ∈ SharedWAL.recoverGroup stream (SharedWAL.reopen wal tail) := by
  apply List.mem_filter.mpr
  exact ⟨SharedWAL.reply_survives_torn_tail wal row tail replied, by simp [belongs]⟩

#print axioms replied_stream_image_survives_torn_tail

end Logkeeper.StreamJournal
