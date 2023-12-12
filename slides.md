---
title: "Incorrectness Logic"
subtitle: |
    | COL731 Course Presentation
    | Based on Peter W. O'Hearn's Paper \& Talk \@ POPL \'20
author:
    - Ramneet Singh
institute: "IIT Delhi"
theme: "Frankfurt"
colortheme: "beaver"
#fonttheme: "professionalfonts"
#mainfont: "Hack Nerd Font"
#fontsize: 10pt
urlcolor: blue
linkstyle: bold
date: October 2023
lang: en-UK
#section-titles: false
toc: true
fontsize: 10pt
# mainfont: "gentium" # See https://fonts.google.com/ for fonts
# sansfont: "Raleway"
# monofont: "IBM Plex Mono"
mathfont: ccmath
header-includes:
 - |
  ```{=latex}
  \usepackage{amsmath,amsfonts,fancyhdr,float,array,amsthm}
  \usepackage[ligature,inference,shorthand]{semantic}
  \usepackage[autostyle=true]{csquotes}
  \floatplacement{figure}{H}
  \usepackage{listings}
  \lstset{basicstyle=\ttfamily,
    showstringspaces=false,
    commentstyle=\color{red},
    keywordstyle=\color{blue}
  }
  \newcommand*{\defeq}{\stackrel{\text{def}}{=}}
  \newcommand{\blue}[1]{\textcolor{blue}{#1}}
  \newcommand{\red}[1]{\textcolor{red}{#1}}
  \newcommand{\green}[1]{\textcolor{LimeGreen}{#1}}
  \newcommand{\false}{\mathrm{false}}
  \newcommand{\true}{\mathrm{true}}
  \newcommand{\Wp}{\mathrm{wp}}
  \newcommand{\Wpp}{\mathrm{wpp}}
  \newcommand{\Body}{\mathrm{Body}}
  \newcommand{\Skip}{\texttt{skip}}
  \newcommand{\Assume}{\texttt{assume}}
  \newcommand{\Error}{\texttt{error}}
  \newcommand{\Nondet}{\texttt{nondet}}
  \newcommand{\Nat}{\mathrm{nat}}
  \newcommand{\ok}{\mathrm{ok}}
  \newcommand{\er}{\mathrm{er}}
  \newcommand{\Vars}{\mathrm{Variables}}
  \newcommand{\Vals}{\mathrm{Values}}
  \newcommand{\sem}[1]{\llbracket\,#1\,\rrbracket}
  \newcommand{\ruleeps}[3]{\blue{[#1]} \; #2 \; \blue{[\epsilon : #3]}}
  \newcommand{\ruleok}[3]{\blue{[#1]} \; #2 \; \green{[\ok : #3]}}
  \newcommand{\ruleer}[3]{\blue{[#1]} \; #2 \; \red{[\er : #3]}}
  \newcommand{\ruleboth}[4]{\blue{[#1]} \; #2 \; \green{[\ok : #3]} \; \red{[\er : #4]}}
  \newcommand{\Mod}{\mathrm{Mod}}
  \newcommand{\Free}{\mathrm{Free}}
  \newcommand{\local}{\texttt{local }}
  
  \newcommand{\beh}{\mathrm{beh}}
  \newcommand{\lbeh}{\mathrm{lbeh}}
  \newcommand{\prp}{\mathrm{prp}}
  \newcommand{\stable}{\mathrm{stable}}
  \newcommand{\vc}{\mathrm{vc}}
  \newcommand{\sat}{\mathrm{sat}}
  \newcommand{\rif}{\mathrm{rif}}
  \newcommand{\writer}{\mathrm{writer}}
  \newcommand{\readers}{\mathrm{readers}}
  \newcommand{\var}{\mathrm{var}}
  \renewcommand{\comp}{\mathrm{comp}}
  \newcommand{\view}{\mathrm{view}}
  \newcommand{\compat}{\mathrm{compat}}
  %\newtheorem{theorem}{Theorem}
  %\newtheorem{lemma}{Lemma}
  \newcommand{\simplies}{\DOTSB\Longrightarrow}
  \newcommand{\simpliedby}{\DOTSB\Longleftarrow}
  \newcommand{\Vbox}{{\setlength{\fboxsep}{0pt}\fbox{\phantom{l}}}}
  ```
---

# Introduction

## Motivation

- Disconnect between Industrial Tools and Academic Theory
    - Sound program logics for reasoning about **correctness**. But code is seldom correct!
    - Industrial automated reasoning tools often **find bugs**

- Q: *Can reasoning about the presence of bugs be underpinned by sound techniques in a principled logical system?*
    - "Reimagine" static-analysis tools
    - Provide symbolic bug-catchers a principled basis

- A: *Underapproximate Reasoning*! (What is that?)

## Underapproximation

- Hoare Logic Specification:
    \begin{center}
    \texttt{\textcolor{red}{\{pre-condition\}} code \textcolor{red}{\{post-condition\}}} \\
    \texttt{\textcolor{red}{post-condition}} $\supseteq$ strongest-post$_{\texttt{code}}$ (\texttt{\textcolor{red}{pre-condition}})
    \end{center}

- Incorrectness Logic Specification:
    \begin{center}
    \texttt{\textcolor{blue}{[presumption]} code \textcolor{blue}{[result]}} \\
    \texttt{\textcolor{blue}{result}} $\subseteq$ strongest-post$_{\texttt{code}}$ (\texttt{\textcolor{blue}{presumption}})
    \end{center}

- Have separate post-assertions for errors, normal termination
    - Assertions describe erroneous states that *can be* reached by actual program executions

## Underapproximation (but picture)

- We obtain a logic which can be used to prove *the presence of bugs, but not their absence*.
    <!-- - \texttt{\textcolor{blue}{result}} assertion is a *positive* result, stating that certain final states can occur. -->
    <!-- - Other final states may occur too -->
    <!-- - Some pre-states may not have successors in \texttt{\textcolor{blue}{result}} -->

![Source: [Incorrectness Logic Paper](https://dl.acm.org/doi/10.1145/3371078)](images/intro.png){height=50%}

\blockquote{\emph{Hoare triples speak the whole truth, where the under-approximate triples speak nothing but the truth.}}

# A Unified Picture (Of Correctness and Incorrectness)

## Category-Theoretic Notion

![Commuting Diagram (Source : [Incorrectness Logic Paper](https://dl.acm.org/doi/10.1145/3371078))](images/comm-diag.png){height=40%}

- \textcolor{blue}{\emph{Predicates}} $\approx 2^{\text{Program States}}$, arrows $\approx$ binary relations on \textcolor{blue}{\emph{Predicates}}
- \emph{post}($c$) is a function, the other two are non-functional

- $\textcolor{blue}{[-]c[-]} = \text{\emph{post}}(c) ; \supseteq$ and $\textcolor{red}{\{-\}c\{-\}} = \text{\emph{post}}(c) ; \subseteq$
- \emph{post}$(c)p$ = strongest post of $p$ = weakest under-approximating post of $p$

## Reasoning Principles - I

![Correctness & Incorrectness Principles (Source : [Incorrectness Logic Paper](https://dl.acm.org/doi/10.1145/3371078))](images/principles-1.png){height=40%}

- $\blue{[p]c[q \lor r]} \implies \blue{[p]c[q]}$ allows you to *drop paths* going forward.
    - Not possible in overapproximate logics - but can *forget information* along each path

- Rules of consequence allow specifications to be adapted to broader contexts

## Reasoning Principles - II

![Correctness & Incorrectness Principles (Source : [Incorrectness Logic Paper](https://dl.acm.org/doi/10.1145/3371078))](images/principles-2.png){height=20%}

![Analogy with Testing (Source : [Incorrectness Logic Paper](https://dl.acm.org/doi/10.1145/3371078))](images/denial.png){height=30%}

- Program testing works on the principle of denial (traditionally, $|u| = |u'| = 1$, a test run)

## Isn't Incorrectness Just Not Correctness?

- Yes, but we aren't powerful enough to precisely compute either!

- \emph{'The inability to prove an over-approximate spec (whether found by a tool or specified by a human) does not imply an error in a program, and neither does not having found a bug imply that there are none: thus, the need for dedicated techniques for each.'}

# Build Your Muscle

## Under-Approximating Triples - I

$$
\blue{[z = 11]}
$$ 

```.cpp
if (x is even) {
    if (y is odd) {
        z = 42;
    }
}
```

$$
\blue{[z = 42]}
$$

. . .

This triple *does not hold*! The state `[z : 42, x : 1, y : 3]` has no predecessor!

## Under-Approximating Triples - II

$$
\blue{[true]}
$$ 

```.cpp
if (x is even) {
    if (y is odd) {
        z = 42;
    }
}
```

$$
\blue{[z = 42]}
$$

. . .

This triple *holds*!

## Under-Approximating Triples - III

$$
\blue{[z = 11]}
$$ 

```.cpp
if (x is even) {
    if (y is odd) {
        z = 42;
    }
}
```

$$
\blue{[z = 42 \land (x \text{ is even }) \land (y \text{ is odd })]}
$$

. . .

This triple *holds*!

## Under-Approximating Triples - IV

$$
\blue{[\true]}
$$ 

```.cpp
if (x is even) {
    if (y is odd) {
        z = 42;
    }
}
```

$$
\blue{[z = 42 \land (x \text{ is even }) \land (y \text{ is odd })]}
$$

. . .

This triple *holds*!

## Specifying Incorrectness

- Reasoning about errors?

. . .

- Have separate result-assertion forms for normal and (erroneous or abnormal) termination. 

```.cpp
void foo(char * str)
/* presumes: [ *str[]==s ]
   achieves: [ er: *str[]==s && length(s) > 16 ] */
{
    char buf[16];
    strcpy(buf,str);
}

int main(int argc, char *argv[])
{ foo(argv[1]); }
```

- Spec: if the length of the input string is greater than 16 then we can get an error (in this case a buffer overflow).

## Under-approximate Success

- Why not over-approximate for successful and under-approximate for erroneous termination?
    - Under-approximate result assertions describing successful computations can help us **soundly discover bugs that come after a procedure is called**.

. . .

```.cpp
void mkeven()
/* presumes: [true], wrong achieves: [ok: x==2 || x==4] */
{ x=2; }

void usemkeven()
{ mkeven(); if (x==4) {error();} }
```

- We don't want false positives!

# Proof System

## Setup

- Simple imperative language. `error()` halts execution and raises an error signal, `er`.

- Abnormal control flows impact reasoning about sequential composition
    - Solution: associate assertions with a set of exit conditions $\epsilon$
    - $\epsilon$ includes (at least) $\ok$ for normal termination and $\er$ causes by `error()`

- $\blue{[p]} C \blue{[\epsilon : q]}$ = $q$ under-approximates the states when $C$ exits via $\epsilon$ starting from states in $p$.

- $x$ is **not** free in $p$ iff $\sigma \in p \iff (\forall v \,.\, (\sigma | x \mapsto v) \in p)$. \red{[BUG]}

- Treat $p,q$ semantically (i.e., any $\subseteq \Sigma$, the set of program states) -- don't fix a language.
    - By treating assertions semantically, we are essentially appealing to mathematics (or set theory) as an oracle in our proof theory when we use $\simplies$ in proof rules.

- $\blue{[p]} C \green{[\ok : q]} \red{[\er : r]}$ as shorthand for $\blue{[p]} C \green{[\ok : q]}$ and $\blue{[p]} C \red{[\er : r]}$.

## Generic Proof Rules - I

![Generic Proof Rules of Incorrectness Logic (Source: [Incorrectness Logic Paper](https://dl.acm.org/doi/10.1145/3371078))](images/generic.png)

## Generic Proof Rules - Axioms

- Valid across different models of states and commands
    - Usual: States = $\Vars \to \Vals$ and Commands = Binary Relations on States
    - Others based on traces, separation logic etc.

\begin{center}
\begin{tabular}{cc}
\inference[Assume]{}{\blue{[p]} \Assume B \green{[\ok : p \land B]} \red{[\er : \false]}} &
\inference[Skip]{}{\blue{[p]} \Skip \green{[\ok : p]} \red{[\er : \false]}} \\ \\
\inference[Empty under-approximates]{}{\blue{[p]} C \blue{[\epsilon:\false]}} &
\end{tabular}
\end{center}

- `assume(B)` statement : `B` is a Boolean expression, can be from an otherwise-unspecified first-order logic signature.

- Axioms for `assume` and `skip` : give the expected assertions for normal termination, but specify `false` (the empty set of states) for abnormal. 

## Generic Proof Rules - Consequence, Disjunction & Choice

\begin{center}
\begin{tabular}{c}
\inference[Consequence]{p' \simpliedby p \quad \blue{[p]} C \blue{[\epsilon:q]} \quad q \simpliedby q'}{\blue{[p']} C \blue{[\epsilon:q']}} \\ \\
\inference[Disjunction]{
    \ruleeps{p_1}{C}{q_1} \quad \ruleeps{p_2}{C}{q_2}
}{
    \ruleeps{p_1 \lor p_2}{C}{q_1 \lor q_2}
} \\ \\
\inference[Choice (where $i=1,2$)]{ \ruleeps{p}{C_i}{q} }{ \ruleeps{p}{C_1 + C_2}{q} }
\end{tabular}
\end{center}

- The rule of consequence lets us *enlarge (weaken) the pre* and *shrink (strengthen) the post-assertion*.
    - Allows us to *drop disjuncts in the post* and *drop conjuncts in the pre*.

- *'Enlarging the pre was used in the Abductor tool ([[Calcagno et al. 2011]](https://www.researchgate.net/publication/220431326_Compositional_Shape_Analysis_by_Means_of_Bi-Abduction), which led to Facebook Infer), when guessing pre-conditions in programs with loops.'*
    - Was unsound in the over-approximating logic used there, required a re-execution step which filtered out unsound pre-conditions

## Generic Proof Rules - Sequencing and Iteration

\begin{center}
\begin{tabular}{cc}
    \emph{Sequencing(short-circuit)} & \emph{Sequencing(normal)} \\ & \\
    \inference[]{
        \ruleer{p}{C_1}{r}
    }{
        \ruleer{p}{C_1;C_2}{r}
    } &
    \inference[]{
        \ruleok{p}{C_1}{q} \quad
        \ruleeps{q}{C_2}{r}
    }{
        \ruleeps{p}{C_1;C_2}{r}
    } \\ & \\
    \emph{Iterate zero} & \emph{Iterate non-zero} \\ & \\
    \inference[]{}{
        \ruleok{p}{C^{*}}{p}
    } &
    \inference[]{
        \ruleeps{p}{C^{*} ; C}{q}
    }{
        \ruleeps{p}{C^{*}}{q}
    }
\end{tabular}
\end{center}

- The *Iterate zero* rule shows that **any assertion is a valid under-approximate invariant for Kleene iteration**.
    - Loop invariants don't play a central role in under-approximate reasoning. Notion of *subvariants* mentioned in [POPL'23 tutorial](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/POPL23TutorialSemanticsPart.pdf).

- The *Iterate non-zero* rule uses $C^{*} ; C$ rather than $C ; C^{*}$ to help reasoning about cases where an error is thrown inside an iteration. Will see an example later.

## Generic Proof Rules - Derived Choice and Iteration, Backwards Variant

\begin{center}
\begin{tabular}{cc}
    \emph{Derived Unrolling Rule} & \emph{Derived Rule of Choice} \\ & \\
    \inference[]{
    \ruleeps{p}{C^i}{q_i} \,,\, \text{ all } i \leq \text{ bound }
}{
    \ruleeps{p}{C^{*}}{ \bigvee_{i \leq \text{bound}} q_i }
} &
    \inference[]{
    \ruleeps{p}{C_1}{q_1} \quad \ruleeps{p}{C_2}{q_2}
}{
    \ruleeps{p}{C_1 + C_2}{q_1 \lor q_2}
}
\end{tabular}
\end{center}

- One of the things that iteration can do is execute its body $i$ times.

- The *Unrolling* rule gives a similar capability symbolic bounded model checking (but we need the *Backwards Variant* rule too in general).

\begin{center}
\begin{tabular}{c}
    \inference[Backwards Variant (where $n$ fresh)]{
    \ruleeps{ p(n) \land \Nat(n) }{C}{ p(n+1) \land \Nat(n) }
}{
    \ruleeps{ p(0) }{C^{*}}{ \exists n \,.\, p(n) \land \Nat(n) }
}
\end{tabular}
\end{center}

- $p(.)$ = a parameterized predicate (a function from expressions to predicates).

## Backwards Variant relation with Program Termination

- $\ruleeps{\text{presumption}}{c}{\text{result}}$ expresses a reachability property that involves termination.
    - *Every state in the result is reachable from some state in the presumption.*

- But this does not imply that a loop must terminate on all executions!
    - Enough paths terminate to cover all the states in result, while other paths may diverge.

- *Backward variant* rule is similar to proof rules for proving program termination (typically use a "variant" that decreases on each loop iteration)
    - But reflects the *backward* nature of this property. $p$ goes down when executing backwards.

- What about the forward variant? $\ruleok{\exists n \,.\, p(n) \land \Nat(n)}{C^{*}}{p(0)}$. 

. . .

- It is always true :)

## Reachability and Liveness

- Liveness : "something (good) will eventually happen".

- Our reachability property:
    - Backwards: For every state in the result, it is possible to eventually reach a state in the pre by executing backwards.

    - Forwards: If we *explore (enumerate pre-states, backtrack, dovetail)* executions from all pre-states, then eventually any given state in the result will be encountered.

- The "eventually" in our forwards does not concern all paths, rather it is an "existential liveness property".

- The over-approximating triple $\red{\{\text{pre}\}}C\red{\{\text{post}\}}$ describes a safety property, that "nothing bad (= not post) will happen".

## Specific Proof Rules - Variables and Mutation

![Rules for Variables and Mutation (Source: [Incorrectness Logic Paper](https://dl.acm.org/doi/10.1145/3371078))](images/specific.png){height=30%}

- Sound when states are functions of type $\Vars \to \Vals$.

- *Mod*$(C)$ is the set of variables modified by assignment statements in $C$, and *Free*$(r)$ is the set of free variables in an assertion $r$. 

- `e` and `nondet()` are syntactically distinct.
    - `e` is an expression built up from a first-order logic signature, can appear within assertions, and is side-effect free.
    - `nondet()` does not appear in assertions.

## Specific Proof Rules - Variables and Mutation

![Rules for Variables and Mutation (Source: [Incorrectness Logic Paper](https://dl.acm.org/doi/10.1145/3371078))](images/specific.png){height=30%}

- Sound when states are functions of type $\Vars \to \Vals$.

- *Mod*$(C)$ is the set of variables modified by assignment statements in $C$, and *Free*$(r)$ is the set of free variables in an assertion $r$. 

- `e` and `nondet()` are syntactically distinct.
    - `e` is an expression built up from a first-order logic signature, can appear within assertions, and is side-effect free.
    - `nondet()` does not appear in assertions. \red{[BUG] in \emph{Nondet Assignment} rule}

## Specific Proof Rules - Assignment

- Incorrectness logic uses Floyd's forward-running assignment axiom rather than Hoare's backwards-running one.

$$
\inference[Assignment]{}{
    \ruleboth{p}{x = e}{\exists x' \,.\, p[x' / x] \land x = e[x' / x]}{\false}
}
$$ 

- Would the below rule be correct?

$$
\inference[Assignment']{}{
    \ruleboth{p[e / x]}{x = e}{p}{\false}
}
$$ 

. . .

- No! For example, $\ruleok{y == 42}{x = 42}{x == y}$ is not valid (take the post-state `[x : 3, y : 3]`).

## Specific Proof Rules - Substitution, Constancy, & Local Variable Rule

\begin{center}
\begin{tabular}{cc}
    \emph{Substitution I} & \emph{Constancy} \\
    $(\Free(e) \cup \{x\}) \cap \Free(C) = \emptyset$ &
    $\Mod(C) \cap \Free(f) = \emptyset$ \\ & \\
    \inference[]{ \ruleeps{p}{C}{q} }{ (\ruleeps{p}{C}{q})(e / x) } &
    \inference[]{ \ruleeps{p}{C}{q} }{ \ruleeps{p \land f}{C}{q \land f} } \\ & \\
    \emph{Substitution II} & \emph{Local Variable} \\
    $y \not\in \Free(p,C,q)$ & $y \not\in \Free(p,C)$ \\ & \\
    \inference[]{ \ruleeps{p}{C}{q} }{ (\ruleeps{p}{C}{q})(y / x) } &
    \inference[]{ \ruleeps{p}{C (y/x)}{q} }{ \ruleeps{p}{\local x \,.\, C}{\exists y \,.\, q} }
\end{tabular}
\end{center}

- The rules of *Substitution*, *Constancy* \& *Consequence* are important for adapting specifications for use in different contexts.

## Exercise: Derive rules for `assert`

- Recall `assert(B) = assume(B) + (assume(!B) ; error())`

$$
\ruleboth{p \land B}{\texttt{assert}(B)}{(p \land B)}{\false}
$$ 

$$
\ruleboth{p \land \neg B}{\texttt{assert}(B)}{\false}{(p \land \neg B)}
$$ 

$$
\ruleboth{p}{\texttt{assert}(B)}{(p \land B)}{(p \land \neg B)}
$$ 

# Reasoning with the Logic

## Setup

- Examples motivated by existing tools, *but* "we are not claiming at this time that incorrectness logic leads to better practical results than these mature tools"

- *'A basic test of a potential foundational formalism is how it expresses a variety of patterns that have arisen naturally.'*

- No formal treatment of procedures. Assume summary-like hypotheses for reasoning.
    $$
    \ruleboth{p}{\texttt{foo()}}{q}{r} \vdash \ruleboth{p'}{C}{q'}{r'}
    $$ 

- *Principle of reuse*: Reason about `foo()`'s body once, don't revisit at call sites (aka summary-based analysis - [COL729](iitd.github.io/col729) throwback)

## `loop0` - I

```.c
void loop0() {
    /* (default presumes is "true" when not specified)
     * achieves: [ok: x>=0 ] */
    int n = nondet();
    x=0;
    while (n > 0) {
        x = x + n;
        n = nondet();
    }}

void client0() { /* achieves: [er: x==200000] */
    loop0();
    if (x == 200000) error(); }
```

- Assuming `loop0` summary, can prove `client0` spec using below followed by sequencing rule.
    $$
    \inference[]{\ruleok{\true}{\texttt{loop0()}}{x \geq 0} \quad x \geq 0 \simpliedby x == 200000}{\ruleok{\true}{\texttt{loop0()}}{x == 200000}}
    $$ 

## `loop0` - II

- How to prove `loop0()` spec?

. . .

- Just unroll once! Then apply *Local Variable* rule + *Unrolling* rule + *Rule of Consequence*.

```.c
[ x==0 ]
    if (n>0) {
        [ x==0 && n>0 ]
        x = x+n; n = nondet(); [ x>0 ]
    } else
    { [ x==0 && n<=0 ] skip;
    }
    [ x>0 || (x==0 && n<=0) ]
        assume (n<=0);
    [ (x>0 && n<=0) || (x==0 && n<=0) ]
[ ok: x>=0 && n<=0 ]
```

## `loop1` - I

```.c
void loop1()
/*  achieves1: [ok: x==0 || x==1 || x==2]
    achieves2: [ok: x>=0] */
{   x = 0;
    Kleene-star {
        x = x + 1;
}   }

void client1()
/* achieves: [er: x==200000] */
{   loop1();
    if ( x==200000 ) error();
}
```

## `loop1` - II

- Infinitely many paths through `loop1()`, and the loop is not guaranteed to terminate.

- *Unrolling* rule: post-conditions for any finite-depth unrollings of the loop. `achieves1`==2 unrollings.

- Not enough to trigger the error in `client1()`. (Unroll 200000 times?)

- Need the backwards variant rule!

$$
\inference[$n$ fresh]{\ruleok{x==n \land \Nat(n)}{x = x+1}{ x == n+1 \land \Nat(n) }}{\ruleok{x==0}{(x = x+1)^{*}}{\exists n \,.\, x==n \land \Nat(n)}}
$$

## `loop2` - I

- Error inside iteration: This is why we need $C^{*};C$, not $C; C^{*}$!

```.c
void loop2()
/* achieves: [er: x==200000] */
{   x = 0;
    Kleene-star{
        if (x==200000) error();
        x = x + 1;
}   }
```

- How can we show this?

## `loop2` - II

- Use *Backwards Variant* rule ($p(n) = 0 \leq x \leq 200000 \land x==n$).
    $$
    \ruleok{x==0}{(\Body)^{*}}{0 \leq x \leq 200000} 
    $$
    $$
    \ruleok{x==0}{(\Body)^{*}}{x == 200000}
    $$ 

. . .

- *Assume* + *Error* + *Sequencing* + *Short-Circuit* gives us
    $$
    \ruleer{x==200000}{\Body}{x==200000}
    $$ 

. . .

- *Sequencing*
    $$
    \ruleer{x==0}{(\Body)^{*} ; \Body}{x==200000}
    $$ 

. . .

- *Iterate non-zero*
    $$
    \ruleer{x==0}{(\Body)^{*}}{x==200000}
    $$ 

<!-- ## `loop3` -->

<!-- - What if we used $C ; C^{*}$? The proof for `loop2()` spec would have 200000 applications of *Sequencing*. -->

<!-- ```.c -->
<!-- void loop3() -->
<!-- /* achieves: [er: x == 200000] */ -->
<!-- { x = nondet(); -->
<!--   Kleene-star { -->
<!--     if (x == 200000) error(); --> 
<!--     x = x + 1; -->
<!-- } } -->
<!-- ``` -->

<!-- . . . -->

<!-- - Can guess a value $k$ returned by `nondet()` and apply *Sequencing* $200000-k$ times. Or -->

<!-- . . . -->

<!-- - Can be `cool` and use *Backwards Variant* to derive more general under-approximate assertions than unrolling, and use the original *Iterate non-zero* to derive an error from the general assertion (with just one $C$ statement). -->
## `loop3`

- What if we used $C ; C^{*}$? The proof for `loop2()` spec would have 200000 applications of *Sequencing*.

```.c
void loop3()
/* achieves: [er: \exists n (x==n /\ n <= 200000)] */
{ y = nondet();
  x = 0;
  Kleene-star {
    if (y == 200000) error(); 
    x = x + 1;
    y = y + 1;
} }
```

. . .

- We don't know the number of iterations it'll take to get an error, and cannot prove the `er` assertion with finitely many unrollings.

. . .

- But we can be `cool` and use *Backwards Variant* to derive more general under-approximate assertions than unrolling, and use the original *Iterate non-zero* to derive an error from the general assertion (with just one $C$ statement).

## Conditionals

- Use of Boolean conditions that are difficult for current theorem provers to deal with causes expressiveness issues.
    - E.g. multiplication goes beyond the decidable subsets of arithmetic encoded in automatic theorem provers.

- How do tools deal with this? And how can Incorrectness Logic deal with this?

## Conditionals - Approach I

```.c
int difficult(int y)
{   return (y*y); /* or hash(y) or obfuscated code */
}

void client()
/* achieves1 : [ok: y==49 && x==1] */
{   int z = nondet();
    if (y == difficult(z))
        x=1;
    else
        x=2;
}
```

- Pragmatic Approach from Dynamic Symbolic Execution: *Concretize symbolic variables*. (replace $z$ with $7$).

- Do this in incorrectness logic by *shrinking the post*. Have `[y==z*z] assume(y==difficult(z)) [ok: y==z*z]` and $y == z*z \simpliedby y==z*z \land z==7$.

## Conditionals - Approach II

```.c
void client()
/* achieves2 : [ok: exists z . (y==difficult(z) && x==1)
    || (y!=difficult(z) && x==2)] */
{   int z = nondet();
    if (y == difficult(z))
        x=1;
    else
        x=2;
}

void test1()
/* achieves: [er: exists z .
    (y==difficult(z) && x==1)
    || (y != difficult(z) && x==2)] */
{   client(); if (x==1 || x==2) error();
}
```

- Record information lazily (hoping difficulty won't matter, like in `test1()`).

## Conditionals - Approach III

```.c
void client()
/* achieves3 : [ok: x==1 || x==2] */
{   int z = nondet();
    if (y == difficult(z))
        x=1;
    else
        x=2;
}

void test2()
{   client(); if (x==2) error(); }
```

- Record disjuncts for both branches, but discard the difficult bits. \red{Unsound!} (e.g. `[x:1, y:3]` not reachable).

- Used for pragmatic reasons in tools like SMART, Infer.RacerD.

- RacerD: it is *an under-approximation of an over-approximation*, where the over-approximation arises by replacing Booleans it doesn't understand with nondeterministic choice.

## Tool Design Insights

 - `Infer.RacerD`: Tools can make localised unsound decisions, which act as assumptions for further sound steps.

 - *'From this perspective, the role of logic is not to produce iron-clad unconditional guarantees, but is to clarify assumptions and their role when making sound inferences.'*

 - `Infer.Pulse`: 20 disjuncts case was ~2.75x wall clock time faster, ~3.1x user time faster, and found 97% of the issues that the 50 disjuncts case found.
    - Choice is not binary! E.g., deploy fast one at code review time, slow one later in the process.

## Flaky Tests - I

- "flaky test" : due to nondeterminism, can give different answers on different runs.

- If $\pi$ is a program path, then
    - $\Wp(\pi)q$: States for which execution of $\pi$ is guaranteed to terminate and satisfy $q$.
    - $\Wpp(\pi)q$: States for which execution of $\pi$ is possible to terminate and satisfy $q$.

- We will use these to obtain pre-assertions, then use forward reasoning to obtain under-approximate post-assertions.

- Why do we need these?
    - Because strongest under-approximate presumptions do not exist in general (see 5.2 in paper).

## Flaky Tests - II

```.c
void foo()
/* sturdy pre [x is even], ach [er: x is even][ok: false]
    flaky pre [x is odd], ach [er: x is odd][ok: x is odd] */
{
    if (x is even) error();
    else { if (nondet()) skip; else error(); }
}

void flakey_client()
/* flaky achieves: [er: x==3 || x==5] */
{   x = 3;
    foo();
    x = x+2;
    assert(x==4);
}
```

- Use $\Wp(\Assume (x \texttt{ is even})) \; \true$ for sturdy presumes, $\Wpp(\Assume(x \texttt{ is odd}); b=\texttt{nondet}(); \Assume ( b )) \; \true$ (where $b$ is local) for flaky presumes.

- A proof of incorrectness can be checked repeatedly in a deterministic fashion. (unclear if this helps)

## Reasoning about Procedures - I

- For a path without procedure calls - say a sequential composition of assignment, assume and assert statements
    - Can perform strongest post-condition reasoning, which is also under-approximate.

- Can combine together pre/post pairs for a number of paths to get an under-approximate summary for a procedure.

- But then using that summary to reason (*soundly*) about a path containing a procedure call is subtle.

- Even in straight-line code, it is *easy* to get a false positive using strongest post-condition reasoning with Hoare logic.

## Reasoning about Procedures - II

```.c
void inc()
/* presumes1: [x>=0], achieves1: [ok: x>0]
   presumes2: [x==m && m>=0], achieves2: [ok: x==m+1 && m>=0] */
{   assert(x>=0);
    x=x+1;
}

void client()
/* presumes1: [x>=0], wrong achieves1: [ok: x>0]
   presumes2: [x==m && m>=0], achieves2: [ok: x==m+2 && m>=0] */
{   inc(); inc(); }

void test()
/* wrong achieves1: [er: x==1]
   achieves2: [er: false] */
{   x = 0;
    client();
    assert(x>=2);
}
```

## Reasoning about Procedures - III

- Incorrectness logic prevents the unsound (for bug catching) inference `presumes1/achieves1` for `client()` and thus `test()`.

- A different spec of `inc()`, given by `presumes2/achieves2`, lets us reason about the composition `inc();inc()` in `client()` more positively, to obtain `presumes2/achieves2` as stated for `client()`. 

- Note: A procedure spec or summary should carry information about free variables and modified - for `inc()`, $x$ is free and modified, $m$ is not free in the procedure body.

- This allows us to apply rules of *Substitution* and *Constancy* to get `client()` spec from `inc()` spec.

## Context and Conclusions

- *'The theory Infer was based on originally ... does not match its use to find bugs rather than to prove their absence.'*

- Led to `RacerD`, `Pulse` program analysers.

- A more general theory of "incorrectness" logic (starting from reverse Hoare logic by de Vries and Koutavas in 2011).

- Related theoretical notions: `wlp` (weakest liberal precondition), `wpp` (weakest possible precondition), dynamic logic.

- Each form of reasoning is as fundamental as the other, they just have different principles. Recall:

> For correctness reasoning, you **get to forget information** as you go along a path, but you **must remember** all the paths.
> For incorrectness reasoning, you **must remember** information as you go along a path, but you **get to forget** some of the paths.

- Possible extensions to other models, concurrency. Possible reuse of work from termination proving.

\begin{center}
    Thank You!
\end{center}

# Appendix

## Backwards Variant - Example I

- For any fixed number of iterations, we can just unfold the *Iterate non-zero* rule and use *Iterate zero*. But no. of iterations may be unknown!

```.c
x = 0;
y = nondet();
while (y != N) do {
    y = y + 1;
    x = x + 1;
}
```
$$
\ruleok{x = 0}{\texttt{while (y != N) do { y = y + 1; x = x + 1 }}}{\exists n \,.\, x == n \land \Nat(n)}
$$ 

## Backwards Variant - Example II

```.c
void loop3()
/* achieves: [er: x == 200000] */
{ x = nondet();
  Kleene-star {
    if (x == 200000) error(); 
    x = x + 1;
} }
```

. . .

- Can guess a value $k$ returned by `nondet()` and apply *Sequencing* $200000-k$ times. Or

. . .

- Can be `cool` and use *Backwards Variant* to derive more general under-approximate assertions than unrolling, and use the original *Iterate non-zero* to derive an error from the general assertion (with just one $C$ statement).
