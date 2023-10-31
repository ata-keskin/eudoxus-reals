# Eudoxus Reals

\begin{abstract}
In this project, we present a peculiar construction of the real numbers, called "Eudoxus reals", using Isabelle/HOL. Similar to the classical method of Dedekind cuts, our approach starts from first principles. However, unlike Dedekind cuts, Eudoxus reals directly derive real numbers from integers, bypassing the intermediate step of constructing rational numbers.

This construction of the real numbers was first discovered by Stephen Schanuel. Schanuel named his construction after the ancient Greek philosopher Eudoxus, who developed a theory of magnitude and proportion to explain the relations between the discrete and the continuous. Our formalization is based on R.D. Arthan’s paper detailing the construction [1]. For establishing the existence of multiplicative inverses for positive slopes, we used the idea of finding a suitable representative from Sławomir Kołodyńaski’s construction on IsarMathLib which is based on Zermelo–Fraenkel set theory.
