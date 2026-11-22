module

public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Formalism.GaussJetBounds.FinalB
public import Mathlib
public import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormEqOneOfNotMem
public import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
public import Formalism.LocalToGlobal.KernelLattices.ColInst

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.DivisionValues (vw)

section Cf

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

end Cf

section AtG

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end AtG

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

end Lat

section AtRec

open Formalism.DivisionValues (PlOver)

end AtRec

section Hyp

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end Hyp

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) {p : ℕ} [Fact p.Prime]

end Rec

section Paths

open Module NumberField IsDedekindDomain

open Formalism.L2.Col Formalism.L2.DIV

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable (Q : KerChain K)

variable {Q} (Bb : ChBas Q)

attribute [instance] LastDat.finCl LastDat.addV LastDat.modV LastDat.finι

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp]

variable (T : LastDat Q.S₁ Bsp)

variable {l : ℕ} [Fact l.Prime] {J : Type} [Fintype J] {Asp : Type} [AddCommGroup Asp] [Module K Asp]

end Generic

section Transport

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable {Q : KerChain K} (G : ChGood Q)

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp] {J : Type}

end Transport

section Place

open Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields}

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

section Entries

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  (Bb : ChBas (recQ Am hK hF hE))

end Entries

section Steps

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  {g : ℕ} [Fact g.Prime] {J : Type}

end Steps

end Record

end Paths

end Formalism.L2.Ker
