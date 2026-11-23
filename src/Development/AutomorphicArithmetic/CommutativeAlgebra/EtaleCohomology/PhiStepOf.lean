module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AdmissibleOfPiDecomposition
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleOfCrystalline
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

private theorem UpperTheory.Ru.crystallineComparison.isGr_comp {Γ Γ' L : Type} [Group Γ] [Group Γ'] [Field L] {d : ℕ}
    {ρ₀ ρ : Γ →* GL (Fin d) L} (f : Γ' →* Γ) (h : UpperTheory.Gal.Int.Geo.IsGr ρ₀ ρ) :
    UpperTheory.Gal.Int.Geo.IsGr (ρ₀.comp f) (ρ.comp f) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g => hc (f g)⟩

theorem UpperTheory.Ru.crystallineComparison.phiStep_of :
    UpperTheory.Ru.crystallineComparison.GeoSide → UpperTheory.Gal.Int.Geo.PhiStep := by
  intro hGeo E Ω _ _ _ _ _ l _ ι H θ hN dd ρ hc hP w hw n ϑ R hcong hR
  obtain ⟨ρ₀, hmat, hgr⟩ := hP
  obtain ⟨h0, hroot⟩ := hR
  intro P AI hT A hA O _ _ _ Bw hj
  have hcr := hGeo E Ω l H θ hN dd ρ₀ hmat w hw n ϑ hcong P AI hT A hA O Bw hj
  have hcont : Continuous (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
    hc.comp continuous_subtype_val
  obtain ⟨LL, r', ϑ', hmod, hcrE, hag, hnil⟩ :=
    UpperTheory.Ru.crystallineComparison.joinQ l P AI hT E Ω _ O Bw _ _ n ϑ dd _ _ hcont
      (UpperTheory.Ru.crystallineComparison.isGr_comp _ hgr) hcr
  refine UpperTheory.Ru.crystallineComparison.nilToPhi l P AI hT ι E Ω A w hA O Bw hj dd _ LL r' hmod hcrE _ hnil R (ι (ϑ 0))
    ((map_ne_zero ι).2 h0) ?_
  rw [← hroot, UpperTheory.Gal.crystallineComparison.heckePol_map, UpperTheory.Gal.crystallineComparison.heckePol_map]
  unfold UpperTheory.Gal.crystallineComparison.heckePol
  refine Finset.sum_congr rfl fun j hj' => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj')
  simp only [RingHom.comp_apply]
  have := hag j hjn
  rw [show algebraMap ↥LL.1 (Formalism.ConjugateSelfDual.Qbar l) (ϑ' j) = ϑ j from this]
