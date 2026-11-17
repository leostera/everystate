# everystate

## 0.4.0

### Minor Changes

- c912576: Remove the `everystate-java` command from the npm package.

### Patch Changes

- 2d4202d: The WebAssembly fallback of the command now exits with the same status as the native binary (12 for an invariant violation, and so on) instead of always 0.

## 0.3.1

### Patch Changes

- f3d05fa: Add the `formal-verification` agent skill (`skills/formal-verification`), with a worked example, and ship it in the npm package.
- 8aa9fbd: Releases now go through changesets, and the crate is published from CI with trusted publishing. No change to the engine.
