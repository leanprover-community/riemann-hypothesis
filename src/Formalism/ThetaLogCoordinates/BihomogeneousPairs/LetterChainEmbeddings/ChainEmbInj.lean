module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LetterAtSuccVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M
open scoped Pointwise

section lat
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

noncomputable def Lat (j : Fin D.T.t → ℕ) (jp : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}

noncomputable def Pt (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (finPos N (D.T.pos i), c)) (fun c => Sum.inl (finPos N (D.T.pos i + 1), c))
    (scalZ N r D.T.t (Fin.castSucc i)) (scalS N r D.T.t (Fin.castSucc i))
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
    (D.T.z i) y

noncomputable def PL (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  L.foldr (fun i acc => Pt p D j jp i acc) y

noncomputable def Pplus (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (Fin.castSucc D.uPos, c)) (fun c => xiVar N r D.T.t c)
    (scalZ N r D.T.t (Fin.last D.T.t)) (scalS N r D.T.t (Fin.last D.T.t))
    (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus y

theorem Pall_eq (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    D.Pall p j jp y = Pplus p D jp (PL p D (List.finRange D.T.t) j jp y) := rfl

variable {p D}

theorem wv_chain (hB : D.BlockOK) (i : Fin D.T.t) (c : Fin r) :
    wv D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i), c) := by
  simp only [wv, chainEmb, Sum.inl.injEq, Prod.mk.injEq, and_true]
  apply Fin.ext
  rw [finPos_pos_val hB, Fin.coe_castSucc, letterAt_pos_val hB]

theorem ev_chain (hB : D.BlockOK) (i : Fin D.T.t) (c : Fin r) :
    ev D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i + 1), c) := by
  simp only [ev, chainEmb, Sum.inl.injEq, Prod.mk.injEq, and_true]
  apply Fin.ext
  rw [finPos_succ_val hB, Fin.coe_castSucc, letterAt_succ_val hB]

theorem chainEmb_inj : Function.Injective (chainEmb N r D.T.t) := by
  intro x y h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
  exact Prod.ext h.1 h.2

theorem xi_notin (c : Fin r) : xiVar N r D.T.t c ∉ Set.range (chainEmb N r D.T.t) := by
  rintro ⟨x, hx⟩
  simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at hx
  exact (Fin.castSucc_lt_last x.1).ne hx.1

theorem supp_gen {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]}
    {mon : BVar N r D.T.t →₀ ℕ} (hm : mon ∈ (rename (chainEmb N r D.T.t) y * g).support) :
    ∃ m1 ∈ y.support, ∃ m2 ∈ g.support, mon = Finsupp.mapDomain (chainEmb N r D.T.t) m1 + m2 := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  rw [MvPolynomial.support_rename_of_injective chainEmb_inj] at ha
  obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨m1, hm1, b, hb, rfl⟩

theorem xi_supp {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {m2 : BVar N r D.T.t →₀ ℕ} (hm2 : m2 ∈ g.support) :
    (∀ v, (∀ c, v ≠ xiVar N r D.T.t c) → m2 v = 0) ∧ ∑ c, m2 (xiVar N r D.T.t c) = b := by
  have h1 := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at h1
  have h2 := h1 hm2
  refine ⟨fun v hv => ?_, h2.2⟩
  by_contra hne
  obtain ⟨c, hc⟩ := h2.1 v (Finsupp.mem_support_iff.mpr hne)
  exact hv c hc

end lat

end Formalism.InvariantFactorPaths.KP.LL
