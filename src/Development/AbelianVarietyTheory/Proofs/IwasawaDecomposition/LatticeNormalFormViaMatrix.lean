module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ToLinNfMatEqSumNfGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal

theorem nfMat_eq_qnf {E : Type} [Field E] (n c : ℕ) (q : E) (e : Fin c → ℤ) (z : Fin n → E) :
    nfMat n c q e z = GlobalTheory.QNF.nfMat n c q e z := by
  funext l s
  unfold nfMat GlobalTheory.QNF.nfMat
  by_cases hs : s.1 < n
  · simp [hs]
  · by_cases hls : l = s
    · subst hls
      simp [hs, Loc.inX]
    · by_cases hn : s.1 = n
      · by_cases hl : l.1 < n
        · simp [hls, hn, hl, Loc.inX]
        · simp [hls, hn, hl, Loc.inX]
      · simp [hs, hls, hn]

theorem nf_matrix : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → ∃ (e : Fin (cOf R j) → ℤ) (z : Fin (R.N j) → X.E), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (fun l : Fin (R.N j + cOf R j) => if hl : l.1 < R.N j then z ⟨l.1, hl⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ∧ (lamYat (Pr := Pr) (R := R) j P).map (h.toLinearMap.restrictScalars (𝓞 X.E)) = (lamYat (Pr := Pr) (R := R) j P).map ((Matrix.toLin' (nfMat (R.N j) (cOf R j) (qOf P : X.E) e z)).restrictScalars (𝓞 X.E)) := by
  intro X Pr R j P hP h hh
  obtain ⟨e, z, h1, h2, h3⟩ := (GlobalTheory.QNF.nf_iff_matNF X Pr R j P hP h).1 hh
  exact ⟨e, z, h1, h2, by rw [nfMat_eq_qnf]; exact h3⟩

end GlobalTheory.Mem.Col2.IdxEx

end
