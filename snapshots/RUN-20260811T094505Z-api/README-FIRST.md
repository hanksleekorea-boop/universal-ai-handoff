# Universal AI Handoff Protocol v4.4

This immutable snapshot uses GitHub Contents API as the latest discovery URL and fixes cross-platform checkout byte drift.

1. Decode the Contents API file wrapper, then verify `MANIFEST.json` and every artifact SHA-256 from commit-pinned raw URLs.
2. Treat Git blob/raw bytes as the integrity authority.
3. Confirm this directory's self-normalizing `.gitattributes` in a fresh checkout before comparing working-tree bytes.
4. Read the verified Korean v4.4 prompt from its first line and execute its bootstrap protocol.

No GitHub authentication or user action is required to read this public snapshot.
