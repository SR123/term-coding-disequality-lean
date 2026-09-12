# Diff of the returned sources against the starting checkpoint

Starting manifest `SHA256SUMS_LEAN_START.txt` (63 files; its own SHA256 is `aac4d677e975c4f4cd7736d921d8691e56ea9bdbf76ce0516d1a5b6fa423de95`, identical to `STARTING_MANIFEST_SHA256SUMS.txt`). Returned manifest `SHA256SUMS_LEAN.txt` (80 files).

## Unchanged (62 files)

All 60 original Lean files, `lake-manifest.json` and `lean-toolchain` are byte-identical to the checkpoint.

## Modified (1 file)

- `lakefile.toml`: `ca71ef8b717a7635` → `fbdf670deafd3995` — the 15 new modules are appended to `defaultTargets` and registered as `[[lean_lib]]` entries; nothing else changed (no pin, no dependency change).

## Added (17 files)

- `AuditMachineRuntime.lean`  `08aa86c4b5846cd1b8b37fe5e6fb22e0af32b18c9a5e01213b9979faa261d758`
- `MCanon.lean`  `065d33fab20046ab36b241033cd938fb826b573a3d2489de1aeb49b68c54ee16`
- `MExamples.lean`  `77c6762e157fedf3fe49b68f25f38f831c9ee950df17d5397e6b01a068f68aeb`
- `MFlow.lean`  `bc63bd6fd6a235cef146ab199ed15d6c5a1ebbde0ab8cd2fb39e3ab6355fff1b`
- `MLib.lean`  `37ab2b242a62883c03c073e62a9a25c907f8d4a1fa99b535fdee26292d04c2e7`
- `MLib2.lean`  `4ecb6ccb5b55305fb6aafe5edcd61be1df6758ef5c11fd98696b2f1c8f89ec41`
- `MLib3.lean`  `9975e5bd7d048a39620f9751fde8ca9e81bf5b5dbc5a962dc855d6b9bafece2e`
- `MMain.lean`  `123e3d5297e3c8264070eb27e469466340f88c07babf59d315d306821698c7af`
- `MNet.lean`  `19fbbc362936d798391d81d84281f38770f9dc03191b319402cd6b3803ed726e`
- `MParse.lean`  `9c5a030a9a15dc3253c06eba6cd438b23fc2c79a20b193b7fe88ab6b58bd1b17`
- `MParseList.lean`  `c5992ce988c9875436fda461f8f49f4793c3190ce3e8fd9eb13d57e8b4d3cb19`
- `MParseRec.lean`  `41a14eb99c40aa1a70165f07e5678abda8ae325b3175215fee865ad1889857ed`
- `MValid.lean`  `11304dcd37cb76f280633e62ea1787f905079bb2278202aa24ee011ebd864974`
- `Machine.lean`  `b71e3dfd34b56c5fd009933db21712cd5db9ccbdd3f88e38bb2c6594ce0996b7`
- `MachineLib.lean`  `f0bb65b679a3ea641fabaca9a2f20578d99487834a5299fd4c6d82bc28b1d397`
- `Ram.lean`  `58b43b1ba4f81a3209c022b5c6d602c10907917139e9a98f948a96145dc7249c`
- `TypesMachineRuntime.lean`  `45f1bcada467e54d8510f9f7fde42dfa3d3e3b2022aa234a996acd144c6ff436`

## Removed

None.
