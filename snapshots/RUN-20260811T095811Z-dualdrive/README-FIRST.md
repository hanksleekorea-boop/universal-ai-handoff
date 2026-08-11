# Universal AI Handoff Protocol v4.5

This immutable snapshot adds two independently owned Google Drive disaster-recovery copies while keeping GitHub Contents API as the primary authority.

1. Decode the GitHub Contents API pointer and verify commit-pinned artifact hashes.
2. Use Drive recovery only when GitHub is unavailable; require matching commit, tree, state digest, and ZIP SHA-256.
3. Never expose account emails, credentials, or private Drive locators in the public repository.
4. Confirm self-normalizing `.gitattributes` in a fresh checkout.
5. Read the verified Korean v4.5 prompt and execute its bootstrap protocol.
