module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_open :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R), B.Cont (maximalIdeal R) → IsOpen ((B.bar O).r.ker : Set F.Γ) ∧ IsOpen ((B.bar O).ad.ker : Set F.Γ) ∧ IsLocallyConstant fun s => ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ B hB
  have hent : ∀ i j, IsLocallyConstant fun s => ((B.bar O).r s).mat i j := fun i j => by
    have hk : ∀ a ∈ maximalIdeal R ^ 1, (res O R : R →+* ResidueField O) a = 0 := fun a ha => by
      rw [pow_one] at ha
      exact (res_eq_zero_iff O R a).2 ha
    exact (hB i j 1).comp (Ideal.Quotient.lift _ (res O R : R →+* ResidueField O) hk)
  have hmat : IsLocallyConstant fun s => ((B.bar O).r s).mat := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h : ∀ᶠ y in nhds x, ∀ i j, ((B.bar O).r y).mat i j = ((B.bar O).r x).mat i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hent i j).eventually_eq x
    exact h.mono fun y hy => Matrix.ext hy
  have hr : IsOpen ((B.bar O).r.ker : Set F.Γ) := by
    have e : ((B.bar O).r.ker : Set F.Γ) =
        {s | ((B.bar O).r s).mat = 1} ∩ (F.del.ker : Set F.Γ) := by
      ext s
      constructor
      · intro hs
        have hs' : (B.bar O).r s = 1 := hs
        refine ⟨?_, ?_⟩
        · show ((B.bar O).r s).mat = 1
          rw [hs']
          rfl
        · show F.del s = 1
          rw [← (B.bar O).nu s, hs']
          rfl
      · rintro ⟨h1, h2⟩
        show (B.bar O).r s = 1
        refine SemidirectProduct.ext (Units.ext h1) ?_
        rw [(B.bar O).nu s]
        exact h2
    rw [e]
    exact (hmat.isOpen_fiber 1).inter hF.del_open
  refine ⟨hr, Subgroup.isOpen_mono (fun s hs => ?_) hr, hmat⟩
  have hs' : (B.bar O).r s = 1 := hs
  show GG.ad n (ResidueField O) ((B.bar O).r s) = 1
  rw [hs', map_one]
