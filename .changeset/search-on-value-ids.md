---
"everystate": patch
---

Values are hash-consed and the search works on their ids: the step cache is keyed on ids, a flat model's states are kept as rows of ids, and a successor's fingerprint is its parent's with the changed terms replaced. On actor-style models one worker takes about 2.2x less CPU and 3x less memory; with `-workers N` the workers use the same path and the merge overlaps them (2x less wall time on 8 workers). Results are unchanged.
