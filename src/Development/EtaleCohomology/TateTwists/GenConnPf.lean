module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.OfRingsLocalSectionsHolds, Development.EtaleCohomology.TateTwists.GenConnPf

-- ===== clump member: Development.EtaleCohomology.TateTwists.OfRingsLocalSectionsHolds =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.OfRingsLocalSectionsHolds", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul\nimport Mathlib.Algebra.Category.ModuleCat.FilteredColimits\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.OfRingsLoc
variable {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))

instance li : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

omit [CommRing R] in
theorem ι_comp_apply {X U : Scheme.{0}} (f : X ⟶ U) (W : X.Opens) (y : X) (h : y ∈ W) :
    (Scheme.Opens.ι W ≫ f) ⟨y, h⟩ = f y :=
  rfl


omit [CommRing R] in
theorem cov_pt {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ S.arrows j := by
  obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have : Scheme.JointlySurjective (Scheme.precoverage.{0} @Etale) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ := (𝒰.X i).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : IsAffine W := hW
  have : Etale (𝒰.f i) := 𝒰.mem₀.2 ⟨i⟩
  refine ⟨W, Scheme.Opens.ι W ≫ 𝒰.f i, ⟨y, hyW⟩, inferInstance, inferInstance, ?_, ?_⟩
  · exact (ι_comp_apply (𝒰.f i) W y hyW).trans hy
  · exact S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) (Scheme.Opens.ι W)

theorem loc_inj {U : Scheme.{0}} (m : M.obj Γ(U, ⊤)) (hm : ofRings.sec M U m = 0) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
      IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0 := by
  have h0 : ConcreteCategory.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)) m =
      ConcreteCategory.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U)) 0 := by
    rw [map_zero]; exact hm
  obtain ⟨V, j, v, hV, hj, hv, hS⟩ := cov_pt _
    (Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) m 0 h0) u
  refine ⟨V, j, v, hV, hj, hv, ?_⟩
  have h1 : ConcreteCategory.hom ((Scheme.Γ ⋙ M).map j.op) m =
      ConcreteCategory.hom ((Scheme.Γ ⋙ M).map j.op) 0 := hS
  rw [map_zero] at h1
  exact h1
end LateralTheory.EtaleFoundations.OfRingsLoc
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.OfRingsLocalSectionsHolds =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.GenConnPf =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.GenConnPf", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp\npublic import Development.EtaleCohomology.TateTwists.OfRingsLocalSectionsHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

def LateralTheory.EtaleFoundations.twF_gen_inj : Prop :=
  ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nontrivial B → ∀ (i : ℤ) (ζ : Prim q B),
    Function.Injective (fun c : ZMod q =>
      (c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj (CommRingCat.of B)) :
        (twF q i).obj (CommRingCat.of B)))

namespace LateralTheory.EtaleFoundations.GenConn

theorem twF_map_mk {q : ℕ} (i : ℤ) {B C : CommRingCat.{0}} (f : B ⟶ C) (ζ : Prim q B) :
    ((twF q i).map f).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (ζ.map f.hom) 1) := by
  show Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single ζ 1)) = _
  erw [Finsupp.mapDomain_single]

theorem inj_of (h : LateralTheory.EtaleFoundations.twF_gen_inj) (q : ℕ) [NeZero q] (U : Scheme.{0}) [Nonempty U] (i : ℤ)
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (fun c : ZMod q => c.val • twGen i ζ) := by
  intro c1 c2 hc
  simp only at hc
  let φ := ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom
  let m : (Scheme.Γ ⋙ twF q i).obj (op U) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have hsec : φ (c1.val • m - c2.val • m) = 0 := by
    rw [map_sub, map_nsmul, map_nsmul]; exact sub_eq_zero.2 hc
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  have hloc : ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
      IsAffine V ∧ Etale j ∧ j v = u ∧
        ((twF q i).map j.appTop).hom (c1.val • m - c2.val • m) = 0 := by
    have h0 : φ (c1.val • m - c2.val • m) = φ 0 := by
      rw [map_zero]; exact hsec
    obtain ⟨V, j, v, hV, hj, hv, hS⟩ := LateralTheory.EtaleFoundations.OfRingsLoc.cov_pt _
      (Presheaf.equalizerSieve_mem Scheme.etaleTopology
        (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) _ 0 h0) u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h1 : ConcreteCategory.hom ((Scheme.Γ ⋙ twF q i).map j.op) (c1.val • m - c2.val • m) =
        ConcreteCategory.hom ((Scheme.Γ ⋙ twF q i).map j.op) 0 := hS
    rw [map_zero] at h1
    exact h1
  obtain ⟨V, j, v, -, -, -, hV⟩ := hloc
  let ψ := ((twF q i).map j.appTop).hom
  have hV2 : ψ (c1.val • m) = ψ (c2.val • m) := sub_eq_zero.1 ((ψ.map_sub _ _).symm.trans hV)
  erw [map_nsmul, map_nsmul] at hV2
  have hm : ψ m = Submodule.Quotient.mk (Finsupp.single (ζ.map j.appTop.hom) 1) := twF_map_mk i j.appTop ζ
  rw [hm] at hV2
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
  haveI : Nontrivial Γ(V, ⊤) := AlgebraicGeometry.Scheme.component_nontrivial V ⊤
  exact h q Γ(V, ⊤) inferInstance i (ζ.map j.appTop.hom) hV2

end LateralTheory.EtaleFoundations.GenConn
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.GenConnPf =====
