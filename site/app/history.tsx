'use client';

import {useEffect, useState} from 'react';

export function PaperHistory() {
  const [expanded, setExpanded] = useState(false);

  useEffect(() => {
    const revealLinkedNote = () => {
      if (window.location.hash === '#authors-note') setExpanded(true);
    };
    revealLinkedNote();
    window.addEventListener('hashchange', revealLinkedNote);
    return () => window.removeEventListener('hashchange', revealLinkedNote);
  }, []);

  return <>
    <h1>
      <a className="paper-title-link" href="#authors-note" onClick={() => setExpanded(true)}>
        One Unit Separates Polynomial Time<br/>from Undecidability in Term Coding
      </a>
    </h1>
    <p className="author">Søren Riis</p>
    <details
      className="authors-note"
      id="authors-note"
      open={expanded}
      onToggle={event => {
        if (event.target === event.currentTarget) setExpanded(event.currentTarget.open);
      }}
    >
      <summary>How this paper developed</summary>
      <div className="authors-note-text">
        <p className="overline">Author’s note · Søren Riis</p>
        <p>
          The ideas behind this paper took shape during my research visit to the
          Institut Henri Poincaré in Paris in early 2016, during the programme
          {' '}<em>Nexus of Information and Computation Theories</em>. I began to see
          how term coding could bring several mathematical questions into a common
          framework. One possibility particularly appealed to me: a seemingly small
          change in a decision problem might produce a dramatic jump from
          polynomial-time decidability to undecidability.
        </p>
        <p>
          These ideas developed into the outline of my omnibus paper. But the
          undecidability argument for what I called the square-matrix decision
          problem remained troublesome. For a long time, I thought a reduction from
          a known undecidable problem should settle it. Repeatedly, however, I
          reached a step I could not justify. The undecidability claim in the
          earlier omnibus version ultimately had to be withdrawn.
        </p>
        <p>
          I came to regard the problem as considerably harder than I had first
          imagined. I subsequently explored it through extended work with AI
          assistants, first Sol Pro in Codex and then Astra Pro in Codex, without
          resolving the central difficulty.
        </p>
        <p>
          The decisive conceptual changes came from me. I proposed reformulating
          the problem by allowing explicit disequality constraints. I also
          recognised that we needed to consider a family of values of <i>k</i>,
          rather than concentrating solely on <span className="history-math"><i>k</i> = 2</span>.
          {' '}These were crucial human contributions: both the modified formulation
          and the recognition that the parameter needed to vary originated in my
          own thinking. The subsequent mathematical development proceeded
          interactively with AI assistance.
        </p>
        <p>
          These changes led to a closely related problem for which the dramatic
          complexity gap could be proved. They recovered the mathematical
          phenomenon I had hoped to capture, while leaving the original square
          problem open.
        </p>
        <p>
          For me, the appeal of the result is partly aesthetic: a minute change in
          the threshold separates polynomial-time decidability from
          undecidability. Its history also matters to me. The finished proof
          conceals years of uncertainty, unsuccessful approaches, and the eventual
          decision to ask a slightly different question.
        </p>
        <p className="history-sources">
          Paris visit:{' '}
          <a href="https://bobaknazer.github.io/csnexus/index.html" target="_blank" rel="noreferrer">programme</a>
          {' · '}
          <a href="https://www.itsoc.org/sites/default/files/2021-01/66nits04-DecWeb%20-1.pdf#page=23" target="_blank" rel="noreferrer">contemporary report (p. 23)</a>.
        </p>
      </div>
    </details>
  </>;
}
