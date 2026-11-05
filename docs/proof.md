# Geneson-type bands with a growing modulus: finitely many monotone 4-term APs of each 2-adic depth

*Partial progress on [Erdős Problem #195](https://www.erdosproblems.com/195). The problem itself remains open, and nothing here decides it.*

## 0. Statements, conventions and credit

**Conventions.** A *permutation of ℤ* is a bijection $H:\mathbb N\to\mathbb Z$, read as the one-sided sequence $H(0),H(1),\dots$ (an ω-permutation). This is the convention of formal-conjectures (`FormalConjectures/ErdosProblems/195.lean`, `f : ℕ ≃ ℤ`). Nothing here concerns doubly infinite arrangements $\mathbb Z\to\mathbb Z$. We write $x\lhd y$ if $x$ comes before $y$ in $H$. A *monotone 4-term AP* of $H$ is a choice of positions $i<j<k<l$ with $(H(i),H(j),H(k),H(l))=(x,x+d,x+2d,x+3d)$ for some $d\ne0$; a negative $d$ gives a decreasing progression. It is recorded by the pair $(x,d)$, so each such progression is counted once. $\nu_2(d)$ is the 2-adic valuation of $d\neq0$.

**Residue convention (essential).** Binary digits and residues of a negative integer are its *true* 2-adic ones (two's complement): $d_i(x)=\lfloor x/2^i\rfloor \bmod 2$ and $x \bmod 2^t\in\{0,\dots,2^t-1\}$, i.e. `Int.ediv`/`Int.emod`. Classing a negative $x$ by $|x| \bmod m$ instead breaks the construction for $m\ge4$. The computation referee of Theorem G found the monotone AP $-6569,-3,6563,13129$ ($m=4$, $a=3$, $4\nmid d$) in that variant; it is not monotone in the construction defined here.

**Theorem G.** For every $t\ge1$ there is a permutation of ℤ with no monotone 4-term AP whose difference is not divisible by $2^t$. (One permutation for each $t$; *not* one permutation for all $t$.)

**Theorem H.** There is one permutation $H$ of ℤ such that for every $j\ge0$ only finitely many monotone 4-term APs of $H$ have $\nu_2(d)=j$. More precisely, for every sequence $t_k\to\infty$ (for instance nondecreasing and unbounded) and every real $a\ge1+\sqrt2$, the permutation $H_{a,t}$ of §2 has no monotone 4-term AP with $|d|\ge \mathcal H(\nu_2(d))$, and every monotone 4-term AP with $\nu_2(d)=j$ also has first term of absolute value below $(5+\frac2a)a^{L_{S(j)}}$; $\mathcal H(j)$ and $S(j)$ are given in the Corollary of §3. Together these bounds give finiteness.

Both theorems are proved in Lean 4 for base $a=3$: Theorem G as stated, and Theorem H for $t_s=s+1$ (§6).

**What survives.** These permutations do have monotone 4-term APs: every one of them has a *seam step* between two consecutive stages inside one residue class (Theorem H(i)–(iv)), and every seam carries such progressions (Prop. 2). So the theorems say nothing about the answer to #195.

**Credit.** The block construction is J. Geneson's ([arXiv:2608.12604](https://arxiv.org/abs/2608.12604), August 2026, §5, (5.2)–(5.3)), built on Adenwalla's geometric residue blocks and on the binary order of Ardal, Brown and Jungić (Geneson §2). Geneson builds, for a fixed $m=2^t$, an integer $a\ge4$ and a truncation constant $2+1/a<c<a$, a 4-permutable *subset* $S_{m,a,c}\subsetneq\mathbb Z$. Taking $c=1$ (no truncation), starting the stages one step earlier and listing $0$ first, the blocks cover all of ℤ. The $m\nmid d$ branches of his Lemmas 5.1–5.5 then exclude every monotone 4-term AP with $m\nmid d$. **Theorem G is an immediate corollary of Geneson's §5.** He does not state it; it was noticed by a Claude Opus 5.5 critic agent reading his §5 with the constants traced. The new ingredient of **Theorem H** is the stage-dependent modulus $m_s=2^{t_s}\to\infty$, which forces ragged band tops (Lemma 2) and separation lemmas across different moduli.

Correspondence with Geneson's lemmas (for constant $t$):
* Lemma 1 below is the alternation of his Lemma 2.1, (2.2)–(2.3), and Lemma 2.2 (Ardal–Brown–Jungić; Hirose–Saito);
* (L1) corresponds to his Lemma 5.1, and (L2) to the opposite-sign bound inside the proof of his Lemma 5.3;
* the step rules (a), (b), (c) are the $m\nmid d$ branches of his Lemmas 5.2, 5.4 and 5.3;
* §3.3 is his Lemma 5.5.

His lemmas assume an integer $a\ge4$, $2+1/a<c<a$, stages $s\ge0$ and a fixed modulus, so they cannot be cited here. Every step is proved below. With $c=1$ only his $m\nmid d$ branches survive: the equal-rank case is the one that needs $c>2+1/a$, and for $m\nmid d$ consecutive same-sign terms never share a residue. For constant $t$ the permutation below is exactly Geneson's blocks with $c=1$, his binary inner order, stage $s$ here being his stage $s-1$, and $0$ first (§2, Remark).

The ℕ analogues are LeSaulnier–Vijay (2011; odd differences) and Adenwalla (arXiv:2211.04451, Theorem 4; every $2^k$). For $t=1,2$, the statement of Theorem G is equivalent to the statement of the earlier repositories [erdos-195-odd-difference](https://github.com/Alex-lop/erdos-195-odd-difference) and [erdos-195-difference-not-div-4](https://github.com/Alex-lop/erdos-195-difference-not-div-4). Their constructions are different: a key order and a reflection merge. As of 2026-11-04 the referees found neither Theorem G nor Theorem H stated in the literature.

## 1. Digits, the 2-adic order and bit-reversed residues

For $x\in\mathbb Z$ and $i\ge0$ let $d_i(x)=\lfloor x/2^i\rfloor\bmod 2$. For $x\ne y$ with $j=\nu_2(y-x)$ we have $d_i(x)=d_i(y)$ for $i<j$ and $d_j(x)\ne d_j(y)$. Put
$$x\prec_2 y\iff d_{\nu_2(y-x)}(x)=0 .$$
This is the lexicographic order of the digit sequences $(d_0(x),d_1(x),\dots)$ (distinct integers have distinct sequences), hence a linear order on ℤ.

**Lemma 1 (alternation).** If $u$ is odd, then $d_j(x+2^ju)=1-d_j(x)$. Hence for an AP $x_0,x_1,x_2,x_3$ with $d=2^ju$, $u$ odd, the truth values $D_i=[d_j(x_i)=0]$ satisfy $D_0=\lnot D_1=D_2$, and $D_i=[x_i\prec_2x_{i+1}]$.

*Proof.* $\lfloor (x+2^ju)/2^j\rfloor=\lfloor x/2^j\rfloor+u$ and $u$ is odd. Since $\nu_2(x_{i+1}-x_i)=j$, the second claim is the definition of $\prec_2$. $\square$

For $n\ge0$ let $\rho_n(x)=\sum_{i<n}d_i(x)\,2^{n-1-i}\in\{0,\dots,2^n-1\}$, the bit-reversed residue of $x$ mod $2^n$ (Geneson's $\rho_{2^n}$). It satisfies $\rho_0=0$ and
$$\rho_{n+1}(x)=2^n\,(x\bmod 2)+\rho_n(\lfloor x/2\rfloor).\tag{1.1}$$

**Lemma F.** (F1) $0\le\rho_n(x)<2^n$. (F2) $\rho_n(x)=\rho_n(y)\iff x\equiv y\pmod{2^n}$. (F3) If $y=x+2^ju$ with $u$ odd and $j<n$, then $\rho_n(x)<\rho_n(y)$ if $d_j(x)=0$, and $\rho_n(y)<\rho_n(x)$ if $d_j(x)=1$; that is, $\rho_n(x)<\rho_n(y)\iff x\prec_2 y$.

*Proof.* (F1) Induction on $n$ via (1.1). (F3) Induction on $n$. If $j=0$, then $x$ and $y$ have different parities. By (1.1) and (F1), the one with last digit $0$ has $\rho_n<2^{n-1}$ and the other has $\rho_n\ge2^{n-1}$. If $j\ge1$, then $x\equiv y\pmod 2$, $\lfloor y/2\rfloor=\lfloor x/2\rfloor+2^{j-1}u$ and $d_j(x)=d_{j-1}(\lfloor x/2\rfloor)$. By (1.1) the comparison reduces to the one for $\lfloor x/2\rfloor$ with $n-1$ and $j-1$. (F2) If $2^n\mid y-x$, then $x\equiv y\pmod2$ and $2^{n-1}\mid\lfloor y/2\rfloor-\lfloor x/2\rfloor$; induct with (1.1). Conversely, if $x\ne y$ and $\rho_n(x)=\rho_n(y)$, write $y-x=2^ju$ with $u$ odd. Then (F3) forces $j\ge n$, so $2^n\mid y-x$. $\square$

## 2. The construction

Fix a real $a>1$ (later $a\ge1+\sqrt2$) and integers $t_1,t_2,\dots\ge0$; put $m_k=2^{t_k}$. Define
$$L_0=0,\qquad L_{k+1}=L_k+2m_{k+1},$$
and for $k\ge0$ the **top exponent**
$$T_k(x)=\begin{cases}L_k+m_{k+1}-\rho_{t_{k+1}}(x),& x<0,\\ L_k+m_{k+1}+1+\rho_{t_{k+1}}(x),& x\ge0.\end{cases}$$
(In the notation of the research note: $A_{k+1}=L_k+m_{k+1}$ and $T_k(x)=\beta_{k+1}(x)$.)

**Lemma 2 (tiling).** $L_k<T_k(x)\le L_{k+1}$. Hence $T_k(x)<T_{k'}(x)$ for $k<k'$, and $T_k(x)\ge 2k+1\to\infty$.

*Proof.* By (F1), $0\le\rho<m_{k+1}$. So $T_k(x)\in[L_k+1,\,L_k+m_{k+1}]$ for $x<0$ and $T_k(x)\in[L_k+m_{k+1}+1,\,L_k+2m_{k+1}]$ for $x\ge0$. For $k<k'$, $T_k(x)\le L_{k+1}\le L_{k'}<T_{k'}(x)$. Finally, $L_k\ge2k$. $\square$

The **stage** $s(x)$ is the least $k$ with $|x|<a^{T_k(x)}$; it exists by Lemma 2. Since $T_k(x)$ increases with $k$, the stage of $x\neq 0$ is $k$ iff
$$a^{T_{k-1}(x)}\le|x|<a^{T_k(x)}\qquad(\text{the lower bound only for }k\ge1),$$
i.e. $x$ lies in the **band** $B_k$ of the research note. Every band is finite, since $|x|<a^{L_{k+1}}$. The bottom of $x$'s band depends on $x\bmod m_k$ and its top on $x\bmod m_{k+1}$; when $m_{k+1}>m_k$ the blocks $B_k\cap\{x\equiv r\ (m_k)\}$ have *ragged tops*.

**Definition of $H=H_{a,t}$.** List $0$ first. Then for $k=0,1,2,\dots$ list the negative elements of $B_k$ in increasing $\prec_2$ order, then the positive elements of $B_k$ in decreasing $\prec_2$ order. The bands are finite and partition $\mathbb Z\setminus\{0\}$, so $H$ is a bijection $\mathbb N\to\mathbb Z$. We use:

* (O1) if $x\lhd y$ and $x,y\ne0$, then $s(x)\le s(y)$;
* (O2) within one stage, negatives come before positives; for two negatives $x\lhd y\iff x\prec_2y$, and for two positives $x\lhd y\iff y\prec_2 x$.

*Remark (Geneson's blocks).* Let $t_k=t$ for all $k$ and $m=2^t$, so $L_k=2mk$. A negative $x$ with $\rho_t(x)=i$ lies in $B_k$ iff $a^{2m(k-1)+m-i}\le|x|<a^{2mk+m-i}$. A positive $x$ with $\rho_t(x)=i$ lies in $B_k$ iff $a^{2m(k-1)+m+1+i}\le x<a^{2mk+m+1+i}$. These are Geneson's $N_{k-1,i}$ and $P_{k-1,i}$ (for $x\equiv r_i$) with $c=1$; our stage $0$ is his missing stage $-1$. By (F3), the order of (O2) lists the blocks of one stage as in his (5.3) and orders each block by his binary order.

## 3. Theorem H

**Theorem H.** Let $a\ge1+\sqrt2$ and let $t_1,t_2,\ldots\ge0$ be arbitrary. Let $x_0\lhd x_1\lhd x_2\lhd x_3$ be an AP with difference $d\ne0$. Then there is $i\in\{1,2\}$ such that, with $s=s(x_i)$ and $U=a^{T_s(x_i)}$:

* (i) $x_i$ and $x_{i+1}$ have the same sign and $|x_i|<|x_{i+1}|$;
* (ii) $s(x_{i+1})=s+1$;
* (iii) $x_i\equiv x_{i+1}\pmod{m_{s+1}}$, so $\nu_2(d)\ge t_{s+1}$;
* (iv) $U\le|x_{i+1}|<(2+\tfrac1a)\,U$.

Such a step $x_i\to x_{i+1}$ is a **seam step**. In particular $|x_i|<a^{L_{s+1}}$, $|d|<|x_{i+1}|<(2+\tfrac1a)a^{L_{s+1}}$ and $|x_0|\le|x_i|+2|d|<(5+\tfrac2a)a^{L_{s+1}}$.

**Corollary.**
(a) *Theorem G.* If $t_k=t$ for all $k\ge1$, every monotone 4-term AP of $H$ has $2^t\mid d$.
(b) If $t_k\to\infty$, put $S(j)=\max\{\sigma\ge1:t_\sigma\le j\}$ and $\mathcal H(j)=(2+\tfrac1a)\,a^{L_{S(j)}}$, with $\mathcal H(j):=0$ when no $\sigma\ge1$ has $t_\sigma\le j$. Then every monotone 4-term AP with $\nu_2(d)=j$ has $|d|<\mathcal H(j)$ and $|x_0|<(5+\tfrac2a)a^{L_{S(j)}}$. So there are only finitely many of them.

*Proof of the Corollary.* (a) is Theorem H(iii). (b) The seam stage $s$ has $t_{s+1}\le\nu_2(d)=j$, so $\sigma=s+1\le S(j)$. By Lemma 2, $L_\sigma\le L_{S(j)}$; apply the bounds after Theorem H. $\square$

With $L_\sigma=A_\sigma+m_\sigma$ this is the bound $(2+\tfrac1a)a^{A_{S(j)}+2^{t_{S(j)}}}$ of the research note. For $t_k=k+1$ (the instance formalized in Lean) we get $t_{s+1}=s+2\le\nu_2(d)$. So this one permutation has no monotone 4-term AP with $4\nmid d$, and those with $\nu_2(d)=v\ge2$ have their seam in a stage $s\le v-2$.

### 3.1 Separation lemmas

**(L1)** Let $x\in B_s$ and $x'\in B_{s'}$ with $s'>s$ and the same sign, and put $\tau=t_{s+1}$. Then $|x'|\ge a^{T_s(x')}$, and $T_s(x')-T_s(x)=\rho_\tau(x)-\rho_\tau(x')$ if $x<0$, $=\rho_\tau(x')-\rho_\tau(x)$ if $x>0$.

*Proof.* $|x'|\ge a^{T_{s'-1}(x')}\ge a^{T_s(x')}$ by the band of $x'$ and Lemma 2 ($s'-1\ge s$, $a>1$). The terms $L_s+m_{s+1}$ (and $+1$) cancel in the difference. $\square$

**(L2)** Let $y\lhd u$ be nonzero of opposite signs, and $s=s(u)$. Then $|y|<a^{T_s(u)-1}$, i.e. $|y|<U(u)/a$ with $U(u)=a^{T_s(u)}$.

*Proof.* Let $\sigma=s(y)$. Since $|y|<a^{T_\sigma(y)}$, it suffices to show $T_\sigma(y)\le T_s(u)-1$.
* $u>0>y$: by (O1), $\sigma\le s$. Then $T_\sigma(y)\le L_\sigma+m_{\sigma+1}\le L_s+m_{s+1}<T_s(u)$. The middle inequality is trivial if $\sigma=s$; if $\sigma<s$ it follows from $L_\sigma+m_{\sigma+1}<L_{\sigma+1}\le L_s$.
* $u<0<y$: the positives of stage $s$ come after its negatives, so $\sigma<s$ by (O1)–(O2). Then $T_\sigma(y)\le L_{\sigma+1}\le L_s<T_s(u)$ by Lemma 2. $\square$

### 3.2 Step rules

Let $d=2^ju$ with $u$ odd. A **step** is a pair $x\to x'=x+d$ of consecutive terms of the AP with the same sign and $x\lhd x'$. It is **appropriate** if $d_j(x)=0$ when $x<0$, and $d_j(x)=1$ when $x>0$. By Lemma 1, this means $x\prec_2x'$ for negatives and $x'\prec_2x$ for positives.

**Lemma 3 (step rules).** Let $x\to x'$ be a step, $s=s(x)$ and $U=a^{T_s(x)}$. Assume (a) $|x'|<|x|$ (a *shrinking* step), or (b/c) $|x'|<(2+\frac1a)U$. Then either the step is appropriate, or it is a seam step: $s(x')>s$, $x\equiv x'\pmod{m_{s+1}}$ and $|x'|\ge U$. In case (a) the step is always appropriate.

*Proof.* By (O1), $s'=s(x')\ge s$. If $s'=s$, the step is appropriate by (O2) and Lemma 1. Let $s'>s$ and $\tau=t_{s+1}$; take $x<0$ (for $x>0$ exchange the roles of $\rho_\tau(x)<\rho_\tau(x')$ and $\rho_\tau(x)>\rho_\tau(x')$).
* If $\rho_\tau(x')<\rho_\tau(x)$, then $T_s(x')\ge T_s(x)+1$ by (L1), so $|x'|\ge aU$. In case (a), $|x'|<|x|<U$, a contradiction. In case (b/c), $|x'|<(2+\frac1a)U\le aU$, a contradiction, because $a\ge2+\frac1a\iff a^2-2a-1\ge0\iff a\ge1+\sqrt2$.
* If $\rho_\tau(x')>\rho_\tau(x)$, then $x\not\equiv x'\pmod{2^\tau}$ by (F2), so $j<\tau$; by (F3), $d_j(x)=0$, and the step is appropriate.
* If $\rho_\tau(x')=\rho_\tau(x)$, then $x\equiv x'\pmod{m_{s+1}}$ by (F2), and $T_s(x')=T_s(x)$, so $|x'|\ge U$ by (L1). This is a seam step; it cannot happen in case (a), since then $|x'|<|x|<U$. $\square$

**Lemma 4 (when (b/c) holds).** Let $x_{i-1},x_i,x_{i+1}$ be consecutive terms with $x_i\to x_{i+1}$ a growing step ($|x_{i+1}|>|x_i|$) and $U=a^{T_{s(x_i)}(x_i)}$. Then $|x_{i+1}|<(2+\frac1a)U$.

*Proof.* We have $|x_i|<U$ and $x_{i+1}=2x_i-x_{i-1}$.
* If $x_{i-1}=0$, then $|x_{i+1}|=2|x_i|<2U$.
* If $x_{i-1}\neq0$ has the sign of $x_i$, then $|x_{i+1}|=2|x_i|-|x_{i-1}|<2U$.
* If $x_{i-1}\ne0$ has the opposite sign, then $|x_{i+1}|=2|x_i|+|x_{i-1}|$, and $|x_{i-1}|<U/a$ by (L2) applied to $x_{i-1}\lhd x_i$. So $|x_{i+1}|<(2+\frac1a)U$. $\square$

**Sign lemma.** The terms $x_0,\dots,x_3$ are strictly monotone. Since $0$ is listed first, only $x_0$ can be $0$, and then $x_1,x_2,x_3$ have one sign and grow in magnitude. If no term is $0$, the signs change at most once; before the change the magnitudes shrink, after it they grow. So the sign pattern is one sign (shrinking or growing), $3+1$, $2+2$, $1+3$, or $x_0=0$.

### 3.3 Case analysis

By Lemma 1, $D_0=\lnot D_1=D_2$, where $D_i=[d_j(x_i)=0]$. An appropriate negative step at $i$ means $D_i$, and an appropriate positive step means $\lnot D_i$. So two consecutive appropriate steps of one sign give $D_i=D_{i+1}$, which is impossible. Suppose that no step $x_i\to x_{i+1}$ with $i\in\{1,2\}$ is a seam step.

* **One sign shrinking, or $3+1$.** The steps $0\to1$ and $1\to2$ have one sign and shrink, so both are appropriate by Lemma 3(a). Contradiction.
* **One sign growing, or $x_0=0$.** The steps $1\to2$ and $2\to3$ have one sign and grow. By Lemmas 4 and 3 they are appropriate. Contradiction.
* **$1+3$.** The steps $1\to2$ (with predecessor of the opposite sign) and $2\to3$ have one sign and grow. By Lemmas 4 and 3 they are appropriate. Contradiction.
* **$2+2$.** Step $0\to1$ shrinks and is appropriate for the sign $\epsilon$ of $x_0,x_1$. Step $2\to3$ grows, and its predecessor $x_1$ has the opposite sign, so it is appropriate for the sign $-\epsilon$. The two conditions are $D_0=[\epsilon=-]$ and $D_2=[-\epsilon=-]=\lnot D_0$, contradicting $D_0=D_2$.

Hence some step $x_i\to x_{i+1}$ with $i\in\{1,2\}$ is a growing seam step. The step $0\to1$ is only ever used as a shrinking step, which is never a seam. Lemma 3 gives (i), (iii) and $|x_{i+1}|\ge U$, and Lemma 4 gives $|x_{i+1}|<(2+\frac1a)U$, so (iv) holds. For (ii): $s(x_{i+1})>s$, and $|x_{i+1}|<(2+\frac1a)U\le aU=a^{T_s(x_i)+1}\le a^{L_{s+1}+1}\le a^{T_{s+1}(x_{i+1})}$ by Lemma 2, so $s(x_{i+1})\le s+1$. Finally, $|x_i|<U\le a^{L_{s+1}}$ and $|d|=|x_{i+1}|-|x_i|<|x_{i+1}|$. $\square$

*Hypotheses on $a$.* The existence of stages and (L1) need $a>1$. Lemma 3(b/c) needs $a\ge2+\frac1a$, i.e. $a\ge1+\sqrt2$; equality is enough. The Lean proof takes $a=3$. Nothing uses $t_k\to\infty$ or monotonicity of $t$ except Corollary (b). For constant $t$ the order inside each Geneson block is never used, since consecutive terms of an AP with $2^t\nmid d$ lie in different residue classes mod $2^t$: Theorem G holds for any order inside the blocks.

## 4. Seams carry progressions (Prop. 2), with a corrected remark

**Prop. 2.** Let $\sigma\ge1$, $A_\sigma=L_{\sigma-1}+m_\sigma$, and $y<0$ with $m_\sigma\mid y$ and $a^{A_\sigma}/2\le|y|<a^{A_\sigma}$. Then $(0,y,2y,3y)$ is a monotone 4-term AP of $H$ (for $a\ge1+\sqrt2$).

*Proof.* Since $m_\sigma\mid y$, $\rho_{t_\sigma}(y)=0$, so $T_{\sigma-1}(y)=A_\sigma$ and $s(y)\le\sigma-1$. The terms $2y,3y$ are also divisible by $m_\sigma$, so $T_{\sigma-1}(2y)=T_{\sigma-1}(3y)=A_\sigma$. Since $|2y|,|3y|\in[a^{A_\sigma},3a^{A_\sigma})$, $s(2y),s(3y)\ge\sigma$. Further $T_\sigma(\cdot)\ge L_\sigma+1=A_\sigma+m_\sigma+1\ge A_\sigma+2$ and $a^2>3$, so $2y,3y\in B_\sigma$. With $j=\nu_2(y)$ we have $d_j(2y)=0$, so $2y\prec_2 3y$ and $2y\lhd3y$ by (O2). Finally, $0$ is first and $y$ is in an earlier stage. $\square$

Lean checks two instances for $a=3$ (`Erdos195Bands.seam_example`, `seam_example_main`):
* $0,-6,-12,-18$ in the Theorem G permutation with $t=1$ ($\sigma=1$, $A_1=2$, $3^2=9$);
* $0,-44,-88,-132$ in the Theorem H permutation with $t_k=k+1$ ($\sigma=1$, $A_1=4$, $3^4=81$, $\nu_2(-44)=2$).

*Corrected remark.* Prop. 2 gives a monotone 4-term AP with $\nu_2(d)=j$ whenever, for some $\sigma\ge1$ with $t_\sigma\le j$, the interval $[a^{A_\sigma}/2,a^{A_\sigma})$ contains an odd multiple of $2^j$. This happens for infinitely many $j$, so $H$ has infinitely many monotone 4-term APs. It happens for every $j\ge\max(t_1,2)$ when $t$ is nondecreasing with $t_{\sigma+1}\le t_\sigma+1$ for all $\sigma$. It can fail for sequences with jumps. The research note claimed that "the set of monotone 4-APs with $\nu_2(d)=j$ is nonempty for every $j\ge t_1$", and that is **false** in general. All three referees found counterexamples. For instance, take $t_1=1$, $t_k=k+10$ for $k\ge2$ (the research note's $t=(1,1,12,13,\dots)$, indexed from $t_0$) and $a=3$. Then $\mathcal H(j)=\tfrac73\cdot3^4=189$ for $1\le j\le11$, so the classes $j=8,\dots,11$ are empty, and an exhaustive search finds class $j=7$ empty too. So Theorem H is not sharp class by class. We only claim that every monotone 4-term AP has a seam step and that every seam $\sigma\ge1$ carries such progressions. We do not claim that the progressions are exactly the seam steps.

## 5. Why the seam progressions survive

A seam is a magnitude cut inside a residue class: in class $r\bmod m_\sigma$, the elements below $a^{T_{\sigma-1}}$ (stage $\sigma-1$) all precede those above it (stage $\sigma$). Across the cut, $x_1\lhd x_2$ is forced by the stage order for *every* pair, including the pairs whose $\prec_2$ direction is wrong. The AP then closes because $x_0\lhd x_1$ and $x_2\lhd x_3$ come out in the appropriate direction automatically (Lemma 1). Inside a band, $\prec_2$ (or its reverse) is the only order that makes every same-sign pair appropriate. Moreover $\prec_2$ has no monotone 3-term AP, so no surviving progression has three terms in one block.

The following is *heuristic* and is not used anywhere. Every stage-monotone band construction has such cuts. Moving the cut, as in the seam variants tested in the research note, only moves the survivors. A cut without survivors would have to grow by a factor $>2+\frac1a$ along every $\prec_2$-descending chain of the class, and that makes the band infinite. A full solution of #195 along these lines would need class restrictions that are not stage-monotone.

## 6. Lean formalization

Lean 4 `v4.35.0`, Mathlib `v4.35.0`, base $a=3$. The construction and the proofs are general in `t : ℕ → ℕ`.

| Here | Lean |
| --- | --- |
| $d_j(x)$, $\rho_n(x)$, with `Int.ediv`/`Int.emod` | `Erdos195Bands.bit`, `Erdos195Bands.rho` (`Erdos195Bands/Digits.lean`) |
| Lemma 1 | `bit_flip`, `bit_cases` |
| Lemma F: (F1), (F2), (F3) | `rho_lt`; `rho_eq_of_dvd` and `dvd_of_rho_eq`; `rho_cmp` |
| $L_k$, $T_k(x)$, $s(x)$ | `L`, `top`, `stage` (`Erdos195Bands/Basic.lean`) |
| Lemma 2; the band of $x$ | `top_bounds`; `abs_lt_stage`, `le_abs_of_lt_stage` |
| the permutation $H_{3,t}$ | `E t`, via an injective `rank t : ℤ → ℕ` |
| (O1), (O2) | `stage_le_of_rank_lt`, `stage_lt_of_rank_lt_pos_neg`, `rho_lt_of_rank_lt_neg`, `rho_lt_of_rank_lt_pos` |
| (L2) | `opp_neg_pos`, `opp_pos_neg` |
| (L1) and Lemma 3 | `step_neg`, `step_pos` |
| §3.3, Lemma 4 | `core` |
| Theorem H, with crude bounds | `exists_seam`: some $s$ with $2^{t_{s+1}}\mid d$, $\lvert x_0\rvert<9\cdot3^{L_{s+1}}$, $\lvert d\rvert<4\cdot3^{L_{s+1}}$ |
| Theorem G | `exists_enum_no_ap` = `Erdos195Bands.finite_depth` |
| Corollary (b), $t_k=k+1$ | `exists_enum_finite` = `Erdos195Bands.main_result` |
| no AP with $4\nmid d$ in that permutation | `E_main_four_dvd` |
| Prop. 2, two instances | `seam_example`, `seam_example_main` |

The rank lists $H$: $0\mapsto0$. For $x$ in stage $s$, put $N=2L_{s+1}$ and $K=2^N$; then a negative $x$ gets $2K+\rho_N(x)$ and a positive $x$ gets $4K-1-\rho_N(x)$. Stage-$s$ ranks lie in $[2K,4K)$, and these intervals increase with $s$. The elements of one half-band are pairwise incongruent mod $2^N$, since $|x-y|<3^{L_{s+1}}\le 2^N$. So by (F3) the order of $\rho_N$ on a half-band is $\prec_2$. The permutation is `(Nat.Subtype.orderIsoOfNat (Set.range (rank t))).toEquiv.trans (Equiv.ofInjective (rank t) _).symm`, as in the depth-2 repository.

Not formalized:
* the general real base $a\ge1+\sqrt2$;
* the precise items (i), (ii), (iv) and the explicit bound $\mathcal H(j)$; Lean proves only the crude bounds above, which suffice for finiteness;
* Prop. 2 in general; Lean proves the two instances;
* the remarks of §5.
