// Code generated by help.awk. DO NOT EDIT.
// GENERATED FILE DO NOT EDIT

package parser

var helpMessages = map[string]HelpMessageBody{
	//line sql.y: 1073
	`ALTER`: {
		//line sql.y: 1074
		Category: hGroup,
		//line sql.y: 1075
		Text: `ALTER TABLE, ALTER INDEX, ALTER VIEW, ALTER SEQUENCE, ALTER DATABASE, ALTER USER
`,
	},
	//line sql.y: 1089
	`ALTER TABLE`: {
		ShortDescription: `change the definition of a table`,
		//line sql.y: 1090
		Category: hDDL,
		//line sql.y: 1091
		Text: `
ALTER TABLE [IF EXISTS] <tablename> <command> [, ...]

Commands:
  ALTER TABLE ... ADD [COLUMN] [IF NOT EXISTS] <colname> <type> [<qualifiers...>]
  ALTER TABLE ... ADD <constraint>
  ALTER TABLE ... DROP [COLUMN] [IF EXISTS] <colname> [RESTRICT | CASCADE]
  ALTER TABLE ... DROP CONSTRAINT [IF EXISTS] <constraintname> [RESTRICT | CASCADE]
  ALTER TABLE ... ALTER [COLUMN] <colname> {SET DEFAULT <expr> | DROP DEFAULT}
  ALTER TABLE ... ALTER [COLUMN] <colname> DROP NOT NULL
  ALTER TABLE ... ALTER [COLUMN] <colname> DROP STORED
  ALTER TABLE ... ALTER [COLUMN] <colname> [SET DATA] TYPE <type> [COLLATE <collation>]
  ALTER TABLE ... RENAME TO <newname>
  ALTER TABLE ... RENAME [COLUMN] <colname> TO <newname>
  ALTER TABLE ... VALIDATE CONSTRAINT <constraintname>
  ALTER TABLE ... SPLIT AT <selectclause>
  ALTER TABLE ... SCATTER [ FROM ( <exprs...> ) TO ( <exprs...> ) ]
  ALTER TABLE ... INJECT STATISTICS ...  (experimental)
  ALTER TABLE ... PARTITION BY RANGE ( <name...> ) ( <rangespec> )
  ALTER TABLE ... PARTITION BY LIST ( <name...> ) ( <listspec> )
  ALTER TABLE ... PARTITION BY NOTHING
  ALTER TABLE ... CONFIGURE ZONE <zoneconfig>
  ALTER PARTITION ... OF TABLE ... CONFIGURE ZONE <zoneconfig>

Column qualifiers:
  [CONSTRAINT <constraintname>] {NULL | NOT NULL | UNIQUE | PRIMARY KEY | CHECK (<expr>) | DEFAULT <expr>}
  FAMILY <familyname>, CREATE [IF NOT EXISTS] FAMILY [<familyname>]
  REFERENCES <tablename> [( <colnames...> )]
  COLLATE <collationname>

Zone configurations:
  DISCARD
  USING <var> = <expr> [, ...]
  { TO | = } <expr>

`,
		//line sql.y: 1126
		SeeAlso: `WEBDOCS/alter-table.html
`,
	},
	//line sql.y: 1140
	`ALTER VIEW`: {
		ShortDescription: `change the definition of a view`,
		//line sql.y: 1141
		Category: hDDL,
		//line sql.y: 1142
		Text: `
ALTER VIEW [IF EXISTS] <name> RENAME TO <newname>
`,
		//line sql.y: 1144
		SeeAlso: `WEBDOCS/alter-view.html
`,
	},
	//line sql.y: 1151
	`ALTER SEQUENCE`: {
		ShortDescription: `change the definition of a sequence`,
		//line sql.y: 1152
		Category: hDDL,
		//line sql.y: 1153
		Text: `
ALTER SEQUENCE [IF EXISTS] <name>
  [INCREMENT <increment>]
  [MINVALUE <minvalue> | NO MINVALUE]
  [MAXVALUE <maxvalue> | NO MAXVALUE]
  [START <start>]
  [[NO] CYCLE]
ALTER SEQUENCE [IF EXISTS] <name> RENAME TO <newname>
`,
	},
	//line sql.y: 1186
	`ALTER USER`: {
		ShortDescription: `change user properties`,
		//line sql.y: 1187
		Category: hPriv,
		//line sql.y: 1188
		Text: `
ALTER USER [IF EXISTS] <name> WITH PASSWORD <password>
`,
		//line sql.y: 1190
		SeeAlso: `CREATE USER
`,
	},
	//line sql.y: 1195
	`ALTER DATABASE`: {
		ShortDescription: `change the definition of a database`,
		//line sql.y: 1196
		Category: hDDL,
		//line sql.y: 1197
		Text: `
ALTER DATABASE <name> RENAME TO <newname>
`,
		//line sql.y: 1199
		SeeAlso: `WEBDOCS/alter-database.html
`,
	},
	//line sql.y: 1207
	`ALTER RANGE`: {
		ShortDescription: `change the parameters of a range`,
		//line sql.y: 1208
		Category: hDDL,
		//line sql.y: 1209
		Text: `
ALTER RANGE <zonename> <command>

Commands:
  ALTER RANGE ... CONFIGURE ZONE <zoneconfig>

Zone configurations:
  DISCARD
  USING <var> = <expr> [, ...]
  { TO | = } <expr>

`,
		//line sql.y: 1220
		SeeAlso: `ALTER TABLE
`,
	},
	//line sql.y: 1225
	`ALTER INDEX`: {
		ShortDescription: `change the definition of an index`,
		//line sql.y: 1226
		Category: hDDL,
		//line sql.y: 1227
		Text: `
ALTER INDEX [IF EXISTS] <idxname> <command>

Commands:
  ALTER INDEX ... RENAME TO <newname>
  ALTER INDEX ... SPLIT AT <selectclause>
  ALTER INDEX ... SCATTER [ FROM ( <exprs...> ) TO ( <exprs...> ) ]

`,
		//line sql.y: 1235
		SeeAlso: `WEBDOCS/alter-index.html
`,
	},
	//line sql.y: 1654
	`BACKUP`: {
		ShortDescription: `back up data to external storage`,
		//line sql.y: 1655
		Category: hCCL,
		//line sql.y: 1656
		Text: `
BACKUP <targets...> TO <location...>
       [ AS OF SYSTEM TIME <expr> ]
       [ INCREMENTAL FROM <location...> ]
       [ WITH <option> [= <value>] [, ...] ]

Targets:
   TABLE <pattern> [, ...]
   DATABASE <databasename> [, ...]

Location:
   "[scheme]://[host]/[path to backup]?[parameters]"

Options:
   INTO_DB
   SKIP_MISSING_FOREIGN_KEYS

`,
		//line sql.y: 1673
		SeeAlso: `RESTORE, WEBDOCS/backup.html
`,
	},
	//line sql.y: 1681
	`RESTORE`: {
		ShortDescription: `restore data from external storage`,
		//line sql.y: 1682
		Category: hCCL,
		//line sql.y: 1683
		Text: `
RESTORE <targets...> FROM <location...>
        [ AS OF SYSTEM TIME <expr> ]
        [ WITH <option> [= <value>] [, ...] ]

Targets:
   TABLE <pattern> [, ...]
   DATABASE <databasename> [, ...]

Locations:
   "[scheme]://[host]/[path to backup]?[parameters]"

Options:
   INTO_DB
   SKIP_MISSING_FOREIGN_KEYS

`,
		//line sql.y: 1699
		SeeAlso: `BACKUP, WEBDOCS/restore.html
`,
	},
	//line sql.y: 1717
	`IMPORT`: {
		ShortDescription: `load data from file in a distributed manner`,
		//line sql.y: 1718
		Category: hCCL,
		//line sql.y: 1719
		Text: `
-- Import both schema and table data:
IMPORT [ TABLE <tablename> FROM ]
       <format> <datafile>
       [ WITH <option> [= <value>] [, ...] ]

-- Import using specific schema, use only table data from external file:
IMPORT TABLE <tablename>
       { ( <elements> ) | CREATE USING <schemafile> }
       <format>
       DATA ( <datafile> [, ...] )
       [ WITH <option> [= <value>] [, ...] ]

Formats:
   CSV
   MYSQLOUTFILE
   MYSQLDUMP (mysqldump's SQL output)
   PGCOPY
   PGDUMP

Options:
   distributed = '...'
   sstsize = '...'
   temp = '...'
   delimiter = '...'      [CSV, PGCOPY-specific]
   nullif = '...'         [CSV, PGCOPY-specific]
   comment = '...'        [CSV-specific]

`,
		//line sql.y: 1747
		SeeAlso: `CREATE TABLE
`,
	},
	//line sql.y: 1797
	`EXPORT`: {
		ShortDescription: `export data to file in a distributed manner`,
		//line sql.y: 1798
		Category: hCCL,
		//line sql.y: 1799
		Text: `
EXPORT INTO <format> (<datafile> [WITH <option> [= value] [,...]]) FROM <query>

Formats:
   CSV

Options:
   delimiter = '...'   [CSV-specific]

`,
		//line sql.y: 1808
		SeeAlso: `SELECT
`,
	},
	//line sql.y: 1903
	`CANCEL`: {
		//line sql.y: 1904
		Category: hGroup,
		//line sql.y: 1905
		Text: `CANCEL JOBS, CANCEL QUERIES, CANCEL SESSIONS
`,
	},
	//line sql.y: 1912
	`CANCEL JOBS`: {
		ShortDescription: `cancel background jobs`,
		//line sql.y: 1913
		Category: hMisc,
		//line sql.y: 1914
		Text: `
CANCEL JOBS <selectclause>
CANCEL JOB <jobid>
`,
		//line sql.y: 1917
		SeeAlso: `SHOW JOBS, PAUSE JOBS, RESUME JOBS
`,
	},
	//line sql.y: 1935
	`CANCEL QUERIES`: {
		ShortDescription: `cancel running queries`,
		//line sql.y: 1936
		Category: hMisc,
		//line sql.y: 1937
		Text: `
CANCEL QUERIES [IF EXISTS] <selectclause>
CANCEL QUERY [IF EXISTS] <expr>
`,
		//line sql.y: 1940
		SeeAlso: `SHOW QUERIES
`,
	},
	//line sql.y: 1971
	`CANCEL SESSIONS`: {
		ShortDescription: `cancel open sessions`,
		//line sql.y: 1972
		Category: hMisc,
		//line sql.y: 1973
		Text: `
CANCEL SESSIONS [IF EXISTS] <selectclause>
CANCEL SESSION [IF EXISTS] <sessionid>
`,
		//line sql.y: 1976
		SeeAlso: `SHOW SESSIONS
`,
	},
	//line sql.y: 2025
	`CREATE`: {
		//line sql.y: 2026
		Category: hGroup,
		//line sql.y: 2027
		Text: `
CREATE DATABASE, CREATE TABLE, CREATE INDEX, CREATE TABLE AS,
CREATE USER, CREATE VIEW, CREATE SEQUENCE, CREATE STATISTICS,
CREATE ROLE
`,
	},
	//line sql.y: 2108
	`CREATE STATISTICS`: {
		ShortDescription: `create a new table statistic (experimental)`,
		//line sql.y: 2109
		Category: hExperimental,
		//line sql.y: 2110
		Text: `
CREATE STATISTICS <statisticname>
  ON <colname> [, ...]
  FROM <tablename>
`,
	},
	//line sql.y: 2173
	`DELETE`: {
		ShortDescription: `delete rows from a table`,
		//line sql.y: 2174
		Category: hDML,
		//line sql.y: 2175
		Text: `DELETE FROM <tablename> [WHERE <expr>]
              [ORDER BY <exprs...>]
              [LIMIT <expr>]
              [RETURNING <exprs...>]
`,
		//line sql.y: 2179
		SeeAlso: `WEBDOCS/delete.html
`,
	},
	//line sql.y: 2194
	`DISCARD`: {
		ShortDescription: `reset the session to its initial state`,
		//line sql.y: 2195
		Category: hCfg,
		//line sql.y: 2196
		Text: `DISCARD ALL
`,
	},
	//line sql.y: 2208
	`DROP`: {
		//line sql.y: 2209
		Category: hGroup,
		//line sql.y: 2210
		Text: `
DROP DATABASE, DROP INDEX, DROP TABLE, DROP VIEW, DROP SEQUENCE,
DROP USER, DROP ROLE
`,
	},
	//line sql.y: 2227
	`DROP VIEW`: {
		ShortDescription: `remove a view`,
		//line sql.y: 2228
		Category: hDDL,
		//line sql.y: 2229
		Text: `DROP VIEW [IF EXISTS] <tablename> [, ...] [CASCADE | RESTRICT]
`,
		//line sql.y: 2230
		SeeAlso: `WEBDOCS/drop-index.html
`,
	},
	//line sql.y: 2242
	`DROP SEQUENCE`: {
		ShortDescription: `remove a sequence`,
		//line sql.y: 2243
		Category: hDDL,
		//line sql.y: 2244
		Text: `DROP SEQUENCE [IF EXISTS] <sequenceName> [, ...] [CASCADE | RESTRICT]
`,
		//line sql.y: 2245
		SeeAlso: `DROP
`,
	},
	//line sql.y: 2257
	`DROP TABLE`: {
		ShortDescription: `remove a table`,
		//line sql.y: 2258
		Category: hDDL,
		//line sql.y: 2259
		Text: `DROP TABLE [IF EXISTS] <tablename> [, ...] [CASCADE | RESTRICT]
`,
		//line sql.y: 2260
		SeeAlso: `WEBDOCS/drop-table.html
`,
	},
	//line sql.y: 2272
	`DROP INDEX`: {
		ShortDescription: `remove an index`,
		//line sql.y: 2273
		Category: hDDL,
		//line sql.y: 2274
		Text: `DROP INDEX [IF EXISTS] <idxname> [, ...] [CASCADE | RESTRICT]
`,
		//line sql.y: 2275
		SeeAlso: `WEBDOCS/drop-index.html
`,
	},
	//line sql.y: 2295
	`DROP DATABASE`: {
		ShortDescription: `remove a database`,
		//line sql.y: 2296
		Category: hDDL,
		//line sql.y: 2297
		Text: `DROP DATABASE [IF EXISTS] <databasename> [CASCADE | RESTRICT]
`,
		//line sql.y: 2298
		SeeAlso: `WEBDOCS/drop-database.html
`,
	},
	//line sql.y: 2318
	`DROP USER`: {
		ShortDescription: `remove a user`,
		//line sql.y: 2319
		Category: hPriv,
		//line sql.y: 2320
		Text: `DROP USER [IF EXISTS] <user> [, ...]
`,
		//line sql.y: 2321
		SeeAlso: `CREATE USER, SHOW USERS
`,
	},
	//line sql.y: 2333
	`DROP ROLE`: {
		ShortDescription: `remove a role`,
		//line sql.y: 2334
		Category: hPriv,
		//line sql.y: 2335
		Text: `DROP ROLE [IF EXISTS] <role> [, ...]
`,
		//line sql.y: 2336
		SeeAlso: `CREATE ROLE, SHOW ROLES
`,
	},
	//line sql.y: 2368
	`EXPLAIN`: {
		ShortDescription: `show the logical plan of a query`,
		//line sql.y: 2369
		Category: hMisc,
		//line sql.y: 2370
		Text: `
EXPLAIN <statement>
EXPLAIN ([PLAN ,] <planoptions...> ) <statement>
EXPLAIN [ANALYZE] (DISTSQL) <statement>
EXPLAIN ANALYZE [(DISTSQL)] <statement>

Explainable statements:
    SELECT, CREATE, DROP, ALTER, INSERT, UPSERT, UPDATE, DELETE,
    SHOW, EXPLAIN

Plan options:
    TYPES, VERBOSE, OPT

`,
		//line sql.y: 2383
		SeeAlso: `WEBDOCS/explain.html
`,
	},
	//line sql.y: 2443
	`PREPARE`: {
		ShortDescription: `prepare a statement for later execution`,
		//line sql.y: 2444
		Category: hMisc,
		//line sql.y: 2445
		Text: `PREPARE <name> [ ( <types...> ) ] AS <query>
`,
		//line sql.y: 2446
		SeeAlso: `EXECUTE, DEALLOCATE, DISCARD
`,
	},
	//line sql.y: 2468
	`EXECUTE`: {
		ShortDescription: `execute a statement prepared previously`,
		//line sql.y: 2469
		Category: hMisc,
		//line sql.y: 2470
		Text: `EXECUTE <name> [ ( <exprs...> ) ]
`,
		//line sql.y: 2471
		SeeAlso: `PREPARE, DEALLOCATE, DISCARD
`,
	},
	//line sql.y: 2492
	`DEALLOCATE`: {
		ShortDescription: `remove a prepared statement`,
		//line sql.y: 2493
		Category: hMisc,
		//line sql.y: 2494
		Text: `DEALLOCATE [PREPARE] { <name> | ALL }
`,
		//line sql.y: 2495
		SeeAlso: `PREPARE, EXECUTE, DISCARD
`,
	},
	//line sql.y: 2515
	`GRANT`: {
		ShortDescription: `define access privileges and role memberships`,
		//line sql.y: 2516
		Category: hPriv,
		//line sql.y: 2517
		Text: `
Grant privileges:
  GRANT {ALL | <privileges...> } ON <targets...> TO <grantees...>
Grant role membership (CCL only):
  GRANT <roles...> TO <grantees...> [WITH ADMIN OPTION]

Privileges:
  CREATE, DROP, GRANT, SELECT, INSERT, DELETE, UPDATE

Targets:
  DATABASE <databasename> [, ...]
  [TABLE] [<databasename> .] { <tablename> | * } [, ...]

`,
		//line sql.y: 2530
		SeeAlso: `REVOKE, WEBDOCS/grant.html
`,
	},
	//line sql.y: 2546
	`REVOKE`: {
		ShortDescription: `remove access privileges and role memberships`,
		//line sql.y: 2547
		Category: hPriv,
		//line sql.y: 2548
		Text: `
Revoke privileges:
  REVOKE {ALL | <privileges...> } ON <targets...> FROM <grantees...>
Revoke role membership (CCL only):
  REVOKE [ADMIN OPTION FOR] <roles...> FROM <grantees...>

Privileges:
  CREATE, DROP, GRANT, SELECT, INSERT, DELETE, UPDATE

Targets:
  DATABASE <databasename> [, <databasename>]...
  [TABLE] [<databasename> .] { <tablename> | * } [, ...]

`,
		//line sql.y: 2561
		SeeAlso: `GRANT, WEBDOCS/revoke.html
`,
	},
	//line sql.y: 2616
	`RESET`: {
		ShortDescription: `reset a session variable to its default value`,
		//line sql.y: 2617
		Category: hCfg,
		//line sql.y: 2618
		Text: `RESET [SESSION] <var>
`,
		//line sql.y: 2619
		SeeAlso: `RESET CLUSTER SETTING, WEBDOCS/set-vars.html
`,
	},
	//line sql.y: 2631
	`RESET CLUSTER SETTING`: {
		ShortDescription: `reset a cluster setting to its default value`,
		//line sql.y: 2632
		Category: hCfg,
		//line sql.y: 2633
		Text: `RESET CLUSTER SETTING <var>
`,
		//line sql.y: 2634
		SeeAlso: `SET CLUSTER SETTING, RESET
`,
	},
	//line sql.y: 2643
	`USE`: {
		ShortDescription: `set the current database`,
		//line sql.y: 2644
		Category: hCfg,
		//line sql.y: 2645
		Text: `USE <dbname>

"USE <dbname>" is an alias for "SET [SESSION] database = <dbname>".
`,
		//line sql.y: 2648
		SeeAlso: `SET SESSION, WEBDOCS/set-vars.html
`,
	},
	//line sql.y: 2669
	`SCRUB`: {
		ShortDescription: `run checks against databases or tables`,
		//line sql.y: 2670
		Category: hExperimental,
		//line sql.y: 2671
		Text: `
EXPERIMENTAL SCRUB TABLE <table> ...
EXPERIMENTAL SCRUB DATABASE <database>

The various checks that ca be run with SCRUB includes:
  - Physical table data (encoding)
  - Secondary index integrity
  - Constraint integrity (NOT NULL, CHECK, FOREIGN KEY, UNIQUE)
`,
		//line sql.y: 2679
		SeeAlso: `SCRUB TABLE, SCRUB DATABASE
`,
	},
	//line sql.y: 2685
	`SCRUB DATABASE`: {
		ShortDescription: `run scrub checks on a database`,
		//line sql.y: 2686
		Category: hExperimental,
		//line sql.y: 2687
		Text: `
EXPERIMENTAL SCRUB DATABASE <database>
                            [AS OF SYSTEM TIME <expr>]

All scrub checks will be run on the database. This includes:
  - Physical table data (encoding)
  - Secondary index integrity
  - Constraint integrity (NOT NULL, CHECK, FOREIGN KEY, UNIQUE)
`,
		//line sql.y: 2695
		SeeAlso: `SCRUB TABLE, SCRUB
`,
	},
	//line sql.y: 2703
	`SCRUB TABLE`: {
		ShortDescription: `run scrub checks on a table`,
		//line sql.y: 2704
		Category: hExperimental,
		//line sql.y: 2705
		Text: `
SCRUB TABLE <tablename>
            [AS OF SYSTEM TIME <expr>]
            [WITH OPTIONS <option> [, ...]]

Options:
  EXPERIMENTAL SCRUB TABLE ... WITH OPTIONS INDEX ALL
  EXPERIMENTAL SCRUB TABLE ... WITH OPTIONS INDEX (<index>...)
  EXPERIMENTAL SCRUB TABLE ... WITH OPTIONS CONSTRAINT ALL
  EXPERIMENTAL SCRUB TABLE ... WITH OPTIONS CONSTRAINT (<constraint>...)
  EXPERIMENTAL SCRUB TABLE ... WITH OPTIONS PHYSICAL
`,
		//line sql.y: 2716
		SeeAlso: `SCRUB DATABASE, SRUB
`,
	},
	//line sql.y: 2776
	`SET CLUSTER SETTING`: {
		ShortDescription: `change a cluster setting`,
		//line sql.y: 2777
		Category: hCfg,
		//line sql.y: 2778
		Text: `SET CLUSTER SETTING <var> { TO | = } <value>
`,
		//line sql.y: 2779
		SeeAlso: `SHOW CLUSTER SETTING, RESET CLUSTER SETTING, SET SESSION,
WEBDOCS/cluster-settings.html
`,
	},
	//line sql.y: 2800
	`SET SESSION`: {
		ShortDescription: `change a session variable`,
		//line sql.y: 2801
		Category: hCfg,
		//line sql.y: 2802
		Text: `
SET [SESSION] <var> { TO | = } <values...>
SET [SESSION] TIME ZONE <tz>
SET [SESSION] CHARACTERISTICS AS TRANSACTION ISOLATION LEVEL { SNAPSHOT | SERIALIZABLE }
SET [SESSION] TRACING { TO | = } { on | off | cluster | local | kv | results } [,...]

`,
		//line sql.y: 2808
		SeeAlso: `SHOW SESSION, RESET, DISCARD, SHOW, SET CLUSTER SETTING, SET TRANSACTION,
WEBDOCS/set-vars.html
`,
	},
	//line sql.y: 2825
	`SET TRANSACTION`: {
		ShortDescription: `configure the transaction settings`,
		//line sql.y: 2826
		Category: hTxn,
		//line sql.y: 2827
		Text: `
SET [SESSION] TRANSACTION <txnparameters...>

Transaction parameters:
   ISOLATION LEVEL { SNAPSHOT | SERIALIZABLE }
   PRIORITY { LOW | NORMAL | HIGH }

`,
		//line sql.y: 2834
		SeeAlso: `SHOW TRANSACTION, SET SESSION,
WEBDOCS/set-transaction.html
`,
	},
	//line sql.y: 3017
	`SHOW`: {
		//line sql.y: 3018
		Category: hGroup,
		//line sql.y: 3019
		Text: `
SHOW BACKUP, SHOW CLUSTER SETTING, SHOW COLUMNS, SHOW CONSTRAINTS,
SHOW CREATE, SHOW DATABASES, SHOW HISTOGRAM, SHOW INDEXES, SHOW JOBS,
SHOW QUERIES, SHOW ROLES, SHOW SESSION, SHOW SESSIONS, SHOW STATISTICS,
SHOW SYNTAX, SHOW TABLES, SHOW TRACE SHOW TRANSACTION, SHOW USERS
`,
	},
	//line sql.y: 3051
	`SHOW SESSION`: {
		ShortDescription: `display session variables`,
		//line sql.y: 3052
		Category: hCfg,
		//line sql.y: 3053
		Text: `SHOW [SESSION] { <var> | ALL }
`,
		//line sql.y: 3054
		SeeAlso: `WEBDOCS/show-vars.html
`,
	},
	//line sql.y: 3075
	`SHOW STATISTICS`: {
		ShortDescription: `display table statistics (experimental)`,
		//line sql.y: 3076
		Category: hExperimental,
		//line sql.y: 3077
		Text: `SHOW STATISTICS [USING JSON] FOR TABLE <table_name>

Returns the available statistics for a table.
The statistics can include a histogram ID, which can
be used with SHOW HISTOGRAM.
If USING JSON is specified, the statistics and histograms
are encoded in JSON format.
`,
		//line sql.y: 3084
		SeeAlso: `SHOW HISTOGRAM
`,
	},
	//line sql.y: 3108
	`SHOW HISTOGRAM`: {
		ShortDescription: `display histogram (experimental)`,
		//line sql.y: 3109
		Category: hExperimental,
		//line sql.y: 3110
		Text: `SHOW HISTOGRAM <histogram_id>

Returns the data in the histogram with the
given ID (as returned by SHOW STATISTICS).
`,
		//line sql.y: 3114
		SeeAlso: `SHOW STATISTICS
`,
	},
	//line sql.y: 3128
	`SHOW BACKUP`: {
		ShortDescription: `list backup contents`,
		//line sql.y: 3129
		Category: hCCL,
		//line sql.y: 3130
		Text: `SHOW BACKUP [FILES|RANGES] <location>
`,
		//line sql.y: 3131
		SeeAlso: `WEBDOCS/show-backup.html
`,
	},
	//line sql.y: 3158
	`SHOW CLUSTER SETTING`: {
		ShortDescription: `display cluster settings`,
		//line sql.y: 3159
		Category: hCfg,
		//line sql.y: 3160
		Text: `
SHOW CLUSTER SETTING <var>
SHOW ALL CLUSTER SETTINGS
`,
		//line sql.y: 3163
		SeeAlso: `WEBDOCS/cluster-settings.html
`,
	},
	//line sql.y: 3180
	`SHOW COLUMNS`: {
		ShortDescription: `list columns in relation`,
		//line sql.y: 3181
		Category: hDDL,
		//line sql.y: 3182
		Text: `SHOW COLUMNS FROM <tablename>
`,
		//line sql.y: 3183
		SeeAlso: `WEBDOCS/show-columns.html
`,
	},
	//line sql.y: 3196
	`SHOW DATABASES`: {
		ShortDescription: `list databases`,
		//line sql.y: 3197
		Category: hDDL,
		//line sql.y: 3198
		Text: `SHOW DATABASES
`,
		//line sql.y: 3199
		SeeAlso: `WEBDOCS/show-databases.html
`,
	},
	//line sql.y: 3207
	`SHOW GRANTS`: {
		ShortDescription: `list grants`,
		//line sql.y: 3208
		Category: hPriv,
		//line sql.y: 3209
		Text: `
Show privilege grants:
  SHOW GRANTS [ON <targets...>] [FOR <users...>]
Show role grants:
  SHOW GRANTS ON ROLE [<roles...>] [FOR <grantees...>]

`,
		//line sql.y: 3215
		SeeAlso: `WEBDOCS/show-grants.html
`,
	},
	//line sql.y: 3228
	`SHOW INDEXES`: {
		ShortDescription: `list indexes`,
		//line sql.y: 3229
		Category: hDDL,
		//line sql.y: 3230
		Text: `SHOW INDEXES FROM <tablename>
`,
		//line sql.y: 3231
		SeeAlso: `WEBDOCS/show-index.html
`,
	},
	//line sql.y: 3264
	`SHOW CONSTRAINTS`: {
		ShortDescription: `list constraints`,
		//line sql.y: 3265
		Category: hDDL,
		//line sql.y: 3266
		Text: `SHOW CONSTRAINTS FROM <tablename>
`,
		//line sql.y: 3267
		SeeAlso: `WEBDOCS/show-constraints.html
`,
	},
	//line sql.y: 3290
	`SHOW QUERIES`: {
		ShortDescription: `list running queries`,
		//line sql.y: 3291
		Category: hMisc,
		//line sql.y: 3292
		Text: `SHOW [CLUSTER | LOCAL] QUERIES
`,
		//line sql.y: 3293
		SeeAlso: `CANCEL QUERIES
`,
	},
	//line sql.y: 3309
	`SHOW JOBS`: {
		ShortDescription: `list background jobs`,
		//line sql.y: 3310
		Category: hMisc,
		//line sql.y: 3311
		Text: `SHOW JOBS
`,
		//line sql.y: 3312
		SeeAlso: `CANCEL JOBS, PAUSE JOBS, RESUME JOBS
`,
	},
	//line sql.y: 3320
	`SHOW TRACE`: {
		ShortDescription: `display an execution trace`,
		//line sql.y: 3321
		Category: hMisc,
		//line sql.y: 3322
		Text: `
SHOW [COMPACT] [KV] TRACE FOR SESSION
`,
		//line sql.y: 3324
		SeeAlso: `EXPLAIN
`,
	},
	//line sql.y: 3347
	`SHOW SESSIONS`: {
		ShortDescription: `list open client sessions`,
		//line sql.y: 3348
		Category: hMisc,
		//line sql.y: 3349
		Text: `SHOW [CLUSTER | LOCAL] SESSIONS
`,
		//line sql.y: 3350
		SeeAlso: `CANCEL SESSIONS
`,
	},
	//line sql.y: 3366
	`SHOW TABLES`: {
		ShortDescription: `list tables`,
		//line sql.y: 3367
		Category: hDDL,
		//line sql.y: 3368
		Text: `SHOW TABLES [FROM <databasename> [ . <schemaname> ] ]
`,
		//line sql.y: 3369
		SeeAlso: `WEBDOCS/show-tables.html
`,
	},
	//line sql.y: 3395
	`SHOW SCHEMAS`: {
		ShortDescription: `list schemas`,
		//line sql.y: 3396
		Category: hDDL,
		//line sql.y: 3397
		Text: `SHOW SCHEMAS [FROM <databasename> ]
`,
	},
	//line sql.y: 3409
	`SHOW SYNTAX`: {
		ShortDescription: `analyze SQL syntax`,
		//line sql.y: 3410
		Category: hMisc,
		//line sql.y: 3411
		Text: `SHOW SYNTAX <string>
`,
	},
	//line sql.y: 3420
	`SHOW TRANSACTION`: {
		ShortDescription: `display current transaction properties`,
		//line sql.y: 3421
		Category: hCfg,
		//line sql.y: 3422
		Text: `SHOW TRANSACTION {ISOLATION LEVEL | PRIORITY | STATUS}
`,
		//line sql.y: 3423
		SeeAlso: `WEBDOCS/show-transaction.html
`,
	},
	//line sql.y: 3442
	`SHOW CREATE`: {
		ShortDescription: `display the CREATE statement for a table, sequence or view`,
		//line sql.y: 3443
		Category: hDDL,
		//line sql.y: 3444
		Text: `SHOW CREATE [ TABLE | SEQUENCE | VIEW ] <tablename>
`,
		//line sql.y: 3445
		SeeAlso: `WEBDOCS/show-create-table.html
`,
	},
	//line sql.y: 3473
	`SHOW USERS`: {
		ShortDescription: `list defined users`,
		//line sql.y: 3474
		Category: hPriv,
		//line sql.y: 3475
		Text: `SHOW USERS
`,
		//line sql.y: 3476
		SeeAlso: `CREATE USER, DROP USER, WEBDOCS/show-users.html
`,
	},
	//line sql.y: 3484
	`SHOW ROLES`: {
		ShortDescription: `list defined roles`,
		//line sql.y: 3485
		Category: hPriv,
		//line sql.y: 3486
		Text: `SHOW ROLES
`,
		//line sql.y: 3487
		SeeAlso: `CREATE ROLE, DROP ROLE
`,
	},
	//line sql.y: 3542
	`SHOW RANGES`: {
		ShortDescription: `list ranges`,
		//line sql.y: 3543
		Category: hMisc,
		//line sql.y: 3544
		Text: `
SHOW EXPERIMENTAL_RANGES FROM TABLE <tablename>
SHOW EXPERIMENTAL_RANGES FROM INDEX [ <tablename> @ ] <indexname>
`,
	},
	//line sql.y: 3790
	`PAUSE JOBS`: {
		ShortDescription: `pause background jobs`,
		//line sql.y: 3791
		Category: hMisc,
		//line sql.y: 3792
		Text: `
PAUSE JOBS <selectclause>
PAUSE JOB <jobid>
`,
		//line sql.y: 3795
		SeeAlso: `SHOW JOBS, CANCEL JOBS, RESUME JOBS
`,
	},
	//line sql.y: 3812
	`CREATE TABLE`: {
		ShortDescription: `create a new table`,
		//line sql.y: 3813
		Category: hDDL,
		//line sql.y: 3814
		Text: `
CREATE TABLE [IF NOT EXISTS] <tablename> ( <elements...> ) [<interleave>]
CREATE TABLE [IF NOT EXISTS] <tablename> [( <colnames...> )] AS <source>

Table elements:
   <name> <type> [<qualifiers...>]
   [UNIQUE | INVERTED] INDEX [<name>] ( <colname> [ASC | DESC] [, ...] )
                           [STORING ( <colnames...> )] [<interleave>]
   FAMILY [<name>] ( <colnames...> )
   [CONSTRAINT <name>] <constraint>

Table constraints:
   PRIMARY KEY ( <colnames...> )
   FOREIGN KEY ( <colnames...> ) REFERENCES <tablename> [( <colnames...> )] [ON DELETE {NO ACTION | RESTRICT}] [ON UPDATE {NO ACTION | RESTRICT}]
   UNIQUE ( <colnames... ) [STORING ( <colnames...> )] [<interleave>]
   CHECK ( <expr> )

Column qualifiers:
  [CONSTRAINT <constraintname>] {NULL | NOT NULL | UNIQUE | PRIMARY KEY | CHECK (<expr>) | DEFAULT <expr>}
  FAMILY <familyname>, CREATE [IF NOT EXISTS] FAMILY [<familyname>]
  REFERENCES <tablename> [( <colnames...> )] [ON DELETE {NO ACTION | RESTRICT}] [ON UPDATE {NO ACTION | RESTRICT}]
  COLLATE <collationname>
  AS ( <expr> ) STORED

Interleave clause:
   INTERLEAVE IN PARENT <tablename> ( <colnames...> ) [CASCADE | RESTRICT]

`,
		//line sql.y: 3841
		SeeAlso: `SHOW TABLES, CREATE VIEW, SHOW CREATE,
WEBDOCS/create-table.html
WEBDOCS/create-table-as.html
`,
	},
	//line sql.y: 4429
	`CREATE SEQUENCE`: {
		ShortDescription: `create a new sequence`,
		//line sql.y: 4430
		Category: hDDL,
		//line sql.y: 4431
		Text: `
CREATE SEQUENCE <seqname>
  [INCREMENT <increment>]
  [MINVALUE <minvalue> | NO MINVALUE]
  [MAXVALUE <maxvalue> | NO MAXVALUE]
  [START [WITH] <start>]
  [CACHE <cache>]
  [NO CYCLE]
  [VIRTUAL]

`,
		//line sql.y: 4441
		SeeAlso: `CREATE TABLE
`,
	},
	//line sql.y: 4496
	`TRUNCATE`: {
		ShortDescription: `empty one or more tables`,
		//line sql.y: 4497
		Category: hDML,
		//line sql.y: 4498
		Text: `TRUNCATE [TABLE] <tablename> [, ...] [CASCADE | RESTRICT]
`,
		//line sql.y: 4499
		SeeAlso: `WEBDOCS/truncate.html
`,
	},
	//line sql.y: 4507
	`CREATE USER`: {
		ShortDescription: `define a new user`,
		//line sql.y: 4508
		Category: hPriv,
		//line sql.y: 4509
		Text: `CREATE USER [IF NOT EXISTS] <name> [ [WITH] PASSWORD <passwd> ]
`,
		//line sql.y: 4510
		SeeAlso: `DROP USER, SHOW USERS, WEBDOCS/create-user.html
`,
	},
	//line sql.y: 4532
	`CREATE ROLE`: {
		ShortDescription: `define a new role`,
		//line sql.y: 4533
		Category: hPriv,
		//line sql.y: 4534
		Text: `CREATE ROLE [IF NOT EXISTS] <name>
`,
		//line sql.y: 4535
		SeeAlso: `DROP ROLE, SHOW ROLES
`,
	},
	//line sql.y: 4553
	`CREATE VIEW`: {
		ShortDescription: `create a new view`,
		//line sql.y: 4554
		Category: hDDL,
		//line sql.y: 4555
		Text: `CREATE VIEW <viewname> [( <colnames...> )] AS <source>
`,
		//line sql.y: 4556
		SeeAlso: `CREATE TABLE, SHOW CREATE, WEBDOCS/create-view.html
`,
	},
	//line sql.y: 4594
	`CREATE INDEX`: {
		ShortDescription: `create a new index`,
		//line sql.y: 4595
		Category: hDDL,
		//line sql.y: 4596
		Text: `
CREATE [UNIQUE | INVERTED] INDEX [IF NOT EXISTS] [<idxname>]
       ON <tablename> ( <colname> [ASC | DESC] [, ...] )
       [STORING ( <colnames...> )] [<interleave>]

Interleave clause:
   INTERLEAVE IN PARENT <tablename> ( <colnames...> ) [CASCADE | RESTRICT]

`,
		//line sql.y: 4604
		SeeAlso: `CREATE TABLE, SHOW INDEXES, SHOW CREATE,
WEBDOCS/create-index.html
`,
	},
	//line sql.y: 4918
	`RELEASE`: {
		ShortDescription: `complete a retryable block`,
		//line sql.y: 4919
		Category: hTxn,
		//line sql.y: 4920
		Text: `RELEASE [SAVEPOINT] cockroach_restart
`,
		//line sql.y: 4921
		SeeAlso: `SAVEPOINT, WEBDOCS/savepoint.html
`,
	},
	//line sql.y: 4929
	`RESUME JOBS`: {
		ShortDescription: `resume background jobs`,
		//line sql.y: 4930
		Category: hMisc,
		//line sql.y: 4931
		Text: `
RESUME JOBS <selectclause>
RESUME JOB <jobid>
`,
		//line sql.y: 4934
		SeeAlso: `SHOW JOBS, CANCEL JOBS, PAUSE JOBS
`,
	},
	//line sql.y: 4951
	`SAVEPOINT`: {
		ShortDescription: `start a retryable block`,
		//line sql.y: 4952
		Category: hTxn,
		//line sql.y: 4953
		Text: `SAVEPOINT cockroach_restart
`,
		//line sql.y: 4954
		SeeAlso: `RELEASE, WEBDOCS/savepoint.html
`,
	},
	//line sql.y: 4969
	`BEGIN`: {
		ShortDescription: `start a transaction`,
		//line sql.y: 4970
		Category: hTxn,
		//line sql.y: 4971
		Text: `
BEGIN [TRANSACTION] [ <txnparameter> [[,] ...] ]
START TRANSACTION [ <txnparameter> [[,] ...] ]

Transaction parameters:
   ISOLATION LEVEL { SNAPSHOT | SERIALIZABLE }
   PRIORITY { LOW | NORMAL | HIGH }

`,
		//line sql.y: 4979
		SeeAlso: `COMMIT, ROLLBACK, WEBDOCS/begin-transaction.html
`,
	},
	//line sql.y: 4992
	`COMMIT`: {
		ShortDescription: `commit the current transaction`,
		//line sql.y: 4993
		Category: hTxn,
		//line sql.y: 4994
		Text: `
COMMIT [TRANSACTION]
END [TRANSACTION]
`,
		//line sql.y: 4997
		SeeAlso: `BEGIN, ROLLBACK, WEBDOCS/commit-transaction.html
`,
	},
	//line sql.y: 5021
	`ROLLBACK`: {
		ShortDescription: `abort the current transaction`,
		//line sql.y: 5022
		Category: hTxn,
		//line sql.y: 5023
		Text: `ROLLBACK [TRANSACTION] [TO [SAVEPOINT] cockroach_restart]
`,
		//line sql.y: 5024
		SeeAlso: `BEGIN, COMMIT, SAVEPOINT, WEBDOCS/rollback-transaction.html
`,
	},
	//line sql.y: 5137
	`CREATE DATABASE`: {
		ShortDescription: `create a new database`,
		//line sql.y: 5138
		Category: hDDL,
		//line sql.y: 5139
		Text: `CREATE DATABASE [IF NOT EXISTS] <name>
`,
		//line sql.y: 5140
		SeeAlso: `WEBDOCS/create-database.html
`,
	},
	//line sql.y: 5209
	`INSERT`: {
		ShortDescription: `create new rows in a table`,
		//line sql.y: 5210
		Category: hDML,
		//line sql.y: 5211
		Text: `
INSERT INTO <tablename> [[AS] <name>] [( <colnames...> )]
       <selectclause>
       [ON CONFLICT [( <colnames...> )] {DO UPDATE SET ... [WHERE <expr>] | DO NOTHING}]
       [RETURNING <exprs...>]
`,
		//line sql.y: 5216
		SeeAlso: `UPSERT, UPDATE, DELETE, WEBDOCS/insert.html
`,
	},
	//line sql.y: 5235
	`UPSERT`: {
		ShortDescription: `create or replace rows in a table`,
		//line sql.y: 5236
		Category: hDML,
		//line sql.y: 5237
		Text: `
UPSERT INTO <tablename> [AS <name>] [( <colnames...> )]
       <selectclause>
       [RETURNING <exprs...>]
`,
		//line sql.y: 5241
		SeeAlso: `INSERT, UPDATE, DELETE, WEBDOCS/upsert.html
`,
	},
	//line sql.y: 5356
	`UPDATE`: {
		ShortDescription: `update rows of a table`,
		//line sql.y: 5357
		Category: hDML,
		//line sql.y: 5358
		Text: `
UPDATE <tablename> [[AS] <name>]
       SET ...
       [WHERE <expr>]
       [ORDER BY <exprs...>]
       [LIMIT <expr>]
       [RETURNING <exprs...>]
`,
		//line sql.y: 5365
		SeeAlso: `INSERT, UPSERT, DELETE, WEBDOCS/update.html
`,
	},
	//line sql.y: 5539
	`<SELECTCLAUSE>`: {
		ShortDescription: `access tabular data`,
		//line sql.y: 5540
		Category: hDML,
		//line sql.y: 5541
		Text: `
Select clause:
  TABLE <tablename>
  VALUES ( <exprs...> ) [ , ... ]
  SELECT ... [ { INTERSECT | UNION | EXCEPT } [ ALL | DISTINCT ] <selectclause> ]
`,
	},
	//line sql.y: 5552
	`SELECT`: {
		ShortDescription: `retrieve rows from a data source and compute a result`,
		//line sql.y: 5553
		Category: hDML,
		//line sql.y: 5554
		Text: `
SELECT [DISTINCT [ ON ( <expr> [ , ... ] ) ] ]
       { <expr> [[AS] <name>] | [ [<dbname>.] <tablename>. ] * } [, ...]
       [ FROM <source> ]
       [ WHERE <expr> ]
       [ GROUP BY <expr> [ , ... ] ]
       [ HAVING <expr> ]
       [ WINDOW <name> AS ( <definition> ) ]
       [ { UNION | INTERSECT | EXCEPT } [ ALL | DISTINCT ] <selectclause> ]
       [ ORDER BY <expr> [ ASC | DESC ] [, ...] ]
       [ LIMIT { <expr> | ALL } ]
       [ OFFSET <expr> [ ROW | ROWS ] ]
`,
		//line sql.y: 5566
		SeeAlso: `WEBDOCS/select-clause.html
`,
	},
	//line sql.y: 5641
	`TABLE`: {
		ShortDescription: `select an entire table`,
		//line sql.y: 5642
		Category: hDML,
		//line sql.y: 5643
		Text: `TABLE <tablename>
`,
		//line sql.y: 5644
		SeeAlso: `SELECT, VALUES, WEBDOCS/table-expressions.html
`,
	},
	//line sql.y: 5932
	`VALUES`: {
		ShortDescription: `select a given set of values`,
		//line sql.y: 5933
		Category: hDML,
		//line sql.y: 5934
		Text: `VALUES ( <exprs...> ) [, ...]
`,
		//line sql.y: 5935
		SeeAlso: `SELECT, TABLE, WEBDOCS/table-expressions.html
`,
	},
	//line sql.y: 6025
	`<SOURCE>`: {
		ShortDescription: `define a data source for SELECT`,
		//line sql.y: 6026
		Category: hDML,
		//line sql.y: 6027
		Text: `
Data sources:
  <tablename> [ @ { <idxname> | <indexhint> } ]
  <tablefunc> ( <exprs...> )
  ( { <selectclause> | <source> } )
  <source> [AS] <alias> [( <colnames...> )]
  <source> { [INNER] | { LEFT | RIGHT | FULL } [OUTER] } JOIN <source> ON <expr>
  <source> { [INNER] | { LEFT | RIGHT | FULL } [OUTER] } JOIN <source> USING ( <colnames...> )
  <source> NATURAL { [INNER] | { LEFT | RIGHT | FULL } [OUTER] } JOIN <source>
  <source> CROSS JOIN <source>
  <source> WITH ORDINALITY
  '[' EXPLAIN ... ']'
  '[' SHOW ... ']'

Index flags:
  '{' FORCE_INDEX = <idxname> [, ...] '}'
  '{' NO_INDEX_JOIN [, ...] '}'

`,
		//line sql.y: 6045
		SeeAlso: `WEBDOCS/table-expressions.html
`,
	},
}
