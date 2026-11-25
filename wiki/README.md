# Proposed Busy Beaver wiki edit

Prepared against **Logical independence**, revision **11626**, dated
24 November 2026 at 13:40:46 UTC:
https://wiki.bbchallenge.org/w/index.php?title=Logical_independence&oldid=11626

## Exact markup

1. Create a page titled **New Foundations consistency machines** using the
   complete contents of
   [New_Foundations_consistency_machines.wiki](New_Foundations_consistency_machines.wiki).
2. In **Logical independence**, insert
   [Logical_independence_update.wiki](Logical_independence_update.wiki)
   within the New Foundations section, after its historical machine table
   and before the existing User-friendly theory subsection.
3. In the first **With Rosser's Axiom of Counting** subsection, replace the
   final sentence of its opening paragraph (the sentence describing 187
   states as the current construction) with:

   ```mediawiki
   The latest construction in this series has 182 working states; see [[New Foundations consistency machines]] and [https://github.com/wlad-svennik/notes/tree/main/nf-axcount-bb182 the release and calibration audit] for its verification scope and the distinction between a smaller implementation and a new arithmetic independence bound.
   ```
4. In **With the Axiom of Cantorian Sets**, replace the final sentence
   describing 199 states as the current machine with:

   ```mediawiki
   The latest construction in this series has 197 working states, with a certificate dated 24 November 2026; see [[New Foundations consistency machines]] and [https://github.com/wlad-svennik/notes/tree/main/nf-cs-bb197 the release and calibration notes].
   ```

Suggested edit summary:

> Add the 173-state NF, 182-state NF + AxCount and 197-state NF + CS constructions, with verification sources and calibration scope.

The source links refer to the three new directories in this repository.
The wiki text should be posted after the repository commit is public.
The wiki has not been edited by this publication task.

## Why this is a construction table

The existing summary table lists upper bounds on theory-specific Busy
Beaver independence thresholds. The new archives establish smaller
literal implementations with the proof boundaries stated in their
READMEs. They do not supply new statements of the exact-table arithmetic
implications needed to transport the PA and Zermelo entries to 173 and
182. The proposal therefore reports the new construction records in a
separate table, and preserves the existing arithmetic-bound entries.

This distinction is about the available arithmetic bridge, not a rule
that mathematical results must be proved in a proof assistant.

## Historical numerical descriptions

The existing discussion of the 187-state Counting presentation describes
that older machine. It should retain its historical number unless its
formula-level account is separately checked against the 182-state source.
The new page identifies full Rosser Counting and full CS without assuming
that every older display formula is a literal description of the new
enumerator.
