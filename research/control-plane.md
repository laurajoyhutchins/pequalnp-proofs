# Research control plane, first slice

Read-only packet ingestion uses the same public gap feed as upstream advisory.yml, and the upstream guard from the freshly fetched upstream revision. It does not call claim, beat, release or submit. The source and observation time are recorded; the revision and snapshot are adjacent observations, not a transaction with the desk.

Run locally with Node 20+:
    node tools/control/packets.mjs /absolute/upstream /absolute/gaps.json /absolute/new-output 2026-11-23T00:00:00Z

The output contains an index and per-gap packet, exact statement bytes and an explicitly unfinished Lean skeleton. Import closure is the upstream guard's conservative source-level closure, not an elaborated Lean dependency index. Missing or invalid closure is a blocker, not a guessed dependency. The packet includes only documented mathematical context fields. No lease data is requested. The public posted list is not live allocation or authoritative verdict data. An absent status or dependency list remains unknown. Existing source at the target path requires reconciliation.

The GitHub workflow runs on workstation changes, manual dispatch or scheduled activation once workstation becomes the default branch. Its first deployment publishes artifacts only; it does not modify refs, cache proof artifacts, or execute candidate code. Access the latest successful research-packets artifact. A later separate publication job may expose a Git-readable index. A missing or stale artifact is not proof of an empty frontier.

Next: unify candidate checking using immutable inputs and the unchanged upstream checker; distinguish checker faults and rejection, then produce receipts and an export under fresh ownership checks. Preserve the separate diagnostic and full-check trust boundaries. Do not shorten worker instructions until the replacement path works end to end.
