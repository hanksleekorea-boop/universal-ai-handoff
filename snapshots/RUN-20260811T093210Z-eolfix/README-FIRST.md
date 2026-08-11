# Universal AI Handoff Protocol v4.3

This immutable snapshot corrects cross-platform checkout byte drift caused by Git EOL conversion.

1. Verify `MANIFEST.json` and every artifact SHA-256 from the commit-pinned raw URLs.
2. Treat Git blob/raw bytes as the integrity authority.
3. Confirm this directory's `.gitattributes` is applied in a fresh checkout before comparing working-tree bytes.
4. Read the verified Korean v4.3 prompt from its first line and execute its bootstrap protocol.

No GitHub authentication or user action is required to read this public snapshot.
