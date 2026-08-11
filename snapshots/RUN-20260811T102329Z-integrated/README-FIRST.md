# Universal AI Handoff Protocol v4.6

This immutable snapshot contains the single integrated prompt for bootstrap, steady updates, read-only runs, recovery, receiving, checkpoints, formal handoff, GitHub publication, and dual-Google-Drive disaster recovery.

1. Verify `MANIFEST.json` and every artifact SHA-256.
2. Read the v4.6 prompt between its standalone BEGIN/END markers exactly once.
3. Apply the unified controller in section 5.
4. On steady runs, read only the project's compact HANDOFF/NOW/LOCK hot path.
5. Treat GitHub as primary; use private Drive recovery only when GitHub is unavailable.

No account identity or private Drive locator is included in this public snapshot.
