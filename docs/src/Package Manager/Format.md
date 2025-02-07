Packages are stored in a database with their hash and the following data:

- `stoloc: int = 0`, which is either 0 (MPMOS0), 1 (MPMOS1). See [[#Storage locations]].

## Storage locations
These are abbreviated as `MPM{TYPE}{N}`.

- MPMOS0 stores objects in a Google Drive.
- MPMOS1 stores objects in an R2 bucket.
- MPMMS stores meta in a D1 SQL database.