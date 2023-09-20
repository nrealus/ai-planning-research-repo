# Example CDCL search

Here is an example of how one would write a search (or solving) function
following the CDCL (Conflict-Driven Clause Learning) algorithm for SAT-solving.

An example brancher is also defined (extending the `Brancher` abstract base class).
This example brancher allows integrating two branchers:
- One that would be active until the first conflict is met,
- And another "main" brancher, which would be active after the first conflict is met.

Moreover, this example brancher allows for geometric restarts.

Note that this is just an example, and no "concrete" branchers have been written yet.

:::src.solver.search