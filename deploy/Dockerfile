FROM scratch

COPY --chmod=0555 logkeeper /usr/local/bin/logkeeper
USER 10001:10001
EXPOSE 5448/tcp
ENTRYPOINT ["/usr/local/bin/logkeeper", "keeper", "--config"]
CMD ["/etc/logkeeper/keeper.json"]
