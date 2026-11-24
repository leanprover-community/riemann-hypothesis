module

public import Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotien
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfLocalCriterionAn, Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfRootListsLocally

-- ===== clump member: Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfLocalCriterionAn =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfLocalCriterionAn", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotien\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass\nimport Mathlib.Algebra.Category.ModuleCat.FilteredColimits\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def muK (q : ℕ) (A : CommRingCat.{0}) : Submodule (ULift.{1} (ZMod q)) ((twF q 1).obj A) :=
  Submodule.span _ {x | ∃ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 ∧
    x = (l.map fun ζ => twGenR A ζ).sum}

theorem muK_gen_map (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q 1).map f).hom (twGenR A ζ) = twGenR B (ζ.map f.hom) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem muK_le (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    muK q A ≤ (muK q B).comap ((twF q 1).map f).hom := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨l, hl, rfl⟩
  refine Submodule.subset_span ⟨l.map (Prim.map f.hom), ?_, ?_⟩
  · have : ((l.map fun ζ => ζ.1).map f.hom).prod = f.hom 1 := by rw [← map_list_prod, hl]
    rw [map_one] at this
    rw [← this, List.map_map, List.map_map]
    rfl
  · rw [map_list_sum, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ζ _
    exact muK_gen_map q f ζ

noncomputable def muT (q : ℕ) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ ((twF q 1).obj A ⧸ muK q A)
  map f := ModuleCat.ofHom (Submodule.mapQ _ _ ((twF q 1).map f).hom (muK_le q f))
  map_id A := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (𝟙 A)).hom x) = Submodule.Quotient.mk x
    rw [(twF q 1).map_id]; rfl
  map_comp f g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (f ≫ g)).hom x) =
      Submodule.Quotient.mk (((twF q 1).map g).hom (((twF q 1).map f).hom x))
    rw [(twF q 1).map_comp]; rfl

noncomputable def muτ (q : ℕ) : twF q 1 ⟶ muT q where
  app A := ModuleCat.ofHom (muK q A).mkQ
  naturality A B f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rfl

theorem muτ_list (q : ℕ) (A : CommRingCat.{0}) (l : List (Prim q A)) (hl : (l.map fun ζ => ζ.1).prod = 1) :
    (l.map fun ζ => ((muτ q).app A).hom (twGenR A ζ)).sum = 0 := by
  have h : (l.map fun ζ => twGenR A ζ).sum ∈ muK q A := Submodule.subset_span ⟨l, hl, rfl⟩
  have := (Submodule.Quotient.mk_eq_zero (muK q A)).2 h
  refine Eq.trans ?_ this
  change _ = ((muτ q).app A).hom (List.map (fun ζ => twGenR A ζ) l).sum
  rw [map_list_sum, List.map_map]
  rfl

def EtaleSheafifyMonoOfKernelLocallyZeroCriterion : Prop :=
  ∀ (q : ℕ) (P Q : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : P ⟶ Q),
    (∀ (U : Scheme.{0}) (x : P.obj Γ(U, ⊤)), (τ.app _).hom x = 0 → Loc U fun _ g => (P.map g.appTop).hom x = 0) →
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ))

def MuRootRelationSubmoduleEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (x : (twF q 1).obj Γ(U, ⊤)), x ∈ muK q Γ(U, ⊤) →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom x = 0

theorem etale_sheafify_mono_of_kernel_locally_zero : EtaleSheafifyMonoOfKernelLocallyZeroCriterion := by
  intro q P Q τ h
  have hli : Presheaf.IsLocallyInjective Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ τ) := by
    refine ⟨fun {X} x y hxy => ?_⟩
    let x' : P.obj Γ(X.unop, ⊤) := x
    let y' : P.obj Γ(X.unop, ⊤) := y
    have hxy' : (τ.app _).hom x' = (τ.app _).hom y' := hxy
    obtain ⟨S, hS, hSP⟩ := h X.unop (x' - y') (by rw [map_sub, hxy', sub_self])
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    have h2 : (P.map g.appTop).hom (x' - y') = 0 := hSP V g hg
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have : Sheaf.IsLocallyInjective ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2 hli
  exact Sheaf.mono_of_isLocallyInjective _

theorem exists_etale_mono_muTwist_quotient_of_locally_zero (h1 : EtaleSheafifyMonoOfKernelLocallyZeroCriterion) (h2 : MuRootRelationSubmoduleEtaleLocallyZero) :
    ExistsEtaleMonoMuTwistKillingRootRelations := by
  intro q _
  refine ⟨muT q, muτ q, h1 q _ _ (muτ q) fun U x hx => h2 q U x ?_, muτ_list q⟩
  exact (Submodule.Quotient.mk_eq_zero (muK q _)).1 hx

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfLocalCriterionAn =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfRootListsLocally =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfRootListsLocally", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfLocalCriterionAn\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def MuRootListProductOneSumEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (l : List (Prim q Γ(U, ⊤))), (l.map fun ζ => ζ.1).prod = 1 →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom (l.map fun ζ => twGenR Γ(U, ⊤) ζ).sum = 0

theorem mu_root_relation_submodule_etale_locally_zero_of_root_lists (h : MuRootListProductOneSumEtaleLocallyZero) : MuRootRelationSubmoduleEtaleLocallyZero := by
  intro q _ U x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact h q U l hl
  | zero => exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨S, hS, hSa⟩ := ha
    obtain ⟨T, hT, hTb⟩ := hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg.1
    have h2 : ((twF q 1).map g.appTop).hom b = 0 := hTb V g hg.2
    show ((twF q 1).map g.appTop).hom (a + b) = 0
    rw [map_add (f := _), h1, h2, add_zero]
  | smul c a _ ha =>
    obtain ⟨S, hS, hSa⟩ := ha
    exact ⟨S, hS, fun V g hg => by
      have h1 : ((twF q 1).map g.appTop).hom a = 0 := hSa V g hg
      show ((twF q 1).map g.appTop).hom (c • a) = 0
      rw [map_smul, h1, smul_zero]⟩

theorem exists_etale_mono_mu_twist_quotient_of_root_lists_locally_zero (h : MuRootListProductOneSumEtaleLocallyZero) : ExistsEtaleMonoMuTwistKillingRootRelations :=
  exists_etale_mono_muTwist_quotient_of_locally_zero etale_sheafify_mono_of_kernel_locally_zero (mu_root_relation_submodule_etale_locally_zero_of_root_lists h)

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfRootListsLocally =====
