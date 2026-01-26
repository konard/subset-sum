---
bump: minor
---

### Added
- Random input generation when CLI arguments are not provided:
  - Numbers set: Random size 1-64 unique numbers, each ranging 1-64
  - Target sum: Random value 1-256
- `rand` dependency for random number generation

### Fixed
- Fixed smart_brute_force algorithm bug where the subset returned was incorrect (returning only the first number instead of the full subset found during preprocessing)
