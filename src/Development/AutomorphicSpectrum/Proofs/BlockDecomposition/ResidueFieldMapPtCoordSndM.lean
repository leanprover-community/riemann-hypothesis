module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Mathlib.FieldTheory.Relrank
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.ResidueField\npublic import Mathlib.Combinatorics.Quiver.ReflQuiver\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors (Z : Scheme.{0}) (t : Z)
    (K : Subfield (Z.residueField t)) (m : Spec (CommRingCat.of K) ⟶ Z)
    (hm : Spec.map (CommRingCat.ofHom K.subtype) ≫ m = Z.fromSpecResidueField t) : K = ⊤ := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective m
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hm
  have hx : x = t := by
    have h := congr($hm (IsLocalRing.closedPoint _))
    have e₁ := Scheme.fromSpecResidueField_apply x
      (Spec.map φ (Spec.map (CommRingCat.ofHom K.subtype) (IsLocalRing.closedPoint _)))
    have e₂ := Scheme.fromSpecResidueField_apply t (IsLocalRing.closedPoint _)
    exact e₁.symm.trans (h.trans e₂)
  subst hx
  rw [← Category.assoc, ← Spec.map_comp] at hm
  have hφ : φ ≫ CommRingCat.ofHom K.subtype = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_id, ← cancel_mono (Z.fromSpecResidueField x), hm]
    exact (Category.id_comp _).symm
  rw [eq_top_iff]
  intro y _
  have hy : K.subtype (φ.hom y) = y := congr($hφ y)
  rw [← hy]
  exact (φ.hom y).2


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.closure_range_residueFieldMap_pullback_eq_top (X Y S : Scheme.{0}) (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) :
    Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom) = ⊤ := by
  set L := Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom)
  let ι : CommRingCat.of L ⟶ (pullback f g).residueField t := CommRingCat.ofHom L.subtype
  let cx : X.residueField (pullback.fst f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.fst f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  let cy : Y.residueField (pullback.snd f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.snd f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
  have hcx : cx ≫ ι = (pullback.fst f g).residueFieldMap t := rfl
  have hcy : cy ≫ ι = (pullback.snd f g).residueFieldMap t := rfl
  have hι : Mono ι := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have e : f (pullback.fst f g t) = g (pullback.snd f g t) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have key : f.residueFieldMap (pullback.fst f g t) ≫ cx =
      (S.residueFieldCongr e).hom ≫ g.residueFieldMap (pullback.snd f g t) ≫ cy := by
    rw [← cancel_mono ι]
    simp only [Category.assoc, hcx, hcy]
    rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
    exact Scheme.Hom.residueFieldMap_congr pullback.condition t
  have hab : (Spec.map cx ≫ X.fromSpecResidueField (pullback.fst f g t)) ≫ f =
      (Spec.map cy ≫ Y.fromSpecResidueField (pullback.snd f g t)) ≫ g := by
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Spec.map_comp_assoc,
      Scheme.residueFieldCongr_fromSpecResidueField]
    rw [Spec.map_comp_assoc]
  have hm : Spec.map (CommRingCat.ofHom L.subtype) ≫ pullback.lift _ _ hab =
      (pullback f g).fromSpecResidueField t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
    · rw [Category.assoc, pullback.lift_snd, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
  exact _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ t L _ hm

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\npublic import Mathlib.FieldTheory.Relrank\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerate\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.FnDeg

open GlobalTheory.ProjSpace

theorem eval_pullRatio_comp {X Y : Scheme.{0}} {N : ℕ} (g : X ⟶ Y) (ψ : Y ⟶ PSpace ℤ N) (x : X)
    (i : Fin (N + 1)) (hx : g x ∈ ψ ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    (g.residueFieldMap x).hom ((Y.evaluation (ψ ⁻¹ᵁ chart ℤ N i) (g x) hx).hom (pullRatio ψ _ i le_rfl j)) =
      (X.evaluation ((g ≫ ψ) ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio (g ≫ ψ) _ i le_rfl j) := by
  have h1 := Scheme.evaluation_naturality_apply g x hx (pullRatio ψ _ i le_rfl j)
  have h2 : g.app (ψ ⁻¹ᵁ chart ℤ N i) (pullRatio ψ _ i le_rfl j) = pullRatio (g ≫ ψ) _ i le_rfl j := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_pullRatio (hi := le_rfl) g le_rfl
  exact h1.trans (congrArg _ h2)

theorem closure_eval_ratio {N : ℕ} (p : PSpace ℤ N) (i : Fin (N + 1)) (hp : p ∈ chart ℤ N i) :
    Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j)) = ⊤ := by
  set K := Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j))
  have hmem : ∀ s, ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom s ∈ K := by
    intro s
    obtain ⟨q, rfl⟩ := aeval_ratio_surjective ℤ N i s
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C]
      simpa using K.intCast_mem a
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact K.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, map_mul, aeval_X]
      exact K.mul_mem ha (Subfield.subset_closure ⟨j, rfl⟩)
  let ρ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (R := Γ(PSpace ℤ N, chart ℤ N i)) (S := K)
      (((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom.codRestrict K hmem)
  refine GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ p K
    (Spec.map ρ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ?_
  rw [← Category.assoc, ← Spec.map_comp]
  have hev : Spec.map ((PSpace ℤ N).evaluation (chart ℤ N i) p hp) ≫ (isAffineOpen_chart ℤ N i).fromSpec =
      (PSpace ℤ N).fromSpecResidueField p := by
    rw [Scheme.fromSpecResidueField, ← (isAffineOpen_chart ℤ N i).fromSpecStalk_eq_fromSpecStalk hp,
      IsAffineOpen.fromSpecStalk, Scheme.evaluation, Spec.map_comp, Category.assoc]
  exact hev

theorem range_residueFieldMap_le {X : Scheme.{0}} {N : ℕ} (φ : X ⟶ PSpace ℤ N) (x : X) (i : Fin (N + 1))
    (hx : x ∈ φ ⁻¹ᵁ chart ℤ N i) :
    Set.range (φ.residueFieldMap x).hom ⊆
      Subfield.closure (Set.range fun j => (X.evaluation (φ ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio φ _ i le_rfl j)) := by
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Subfield.closure (Set.range fun j =>
      ((PSpace ℤ N).evaluation (chart ℤ N i) (φ x) hx).hom (ratio ℤ N i j)) := by
    have hc := closure_eval_ratio (φ x) i hx
    rw [hc]
    exact Subfield.mem_top a
  have h1 : (φ.residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
  rw [RingHom.map_field_closure] at h1
  refine Subfield.closure_mono ?_ h1
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨j, ?_⟩
  have h2 := Scheme.evaluation_naturality_apply φ x hx (ratio ℤ N i j)
  rw [Scheme.Hom.app_eq_appLE] at h2
  exact h2.symm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp only [ptCoord, pullRatio_self, map_one]

theorem range_prB_le (x : MP ℤ m n) (k : Fin (m + 1)) :
    Set.range ((prB n k).residueFieldMap x).hom ⊆ Subfield.closure (Set.range (ptCoord x)) := by
  refine (range_residueFieldMap_le (prB n k) x (ptChart x k) (mem_ptChart x k)).trans ?_
  refine Subfield.closure_le.2 ?_
  rintro _ ⟨j, rfl⟩
  exact Subfield.subset_closure ⟨⟨k, j⟩, rfl⟩

abbrev sndM (m : ℕ) (n : Fin (m + 2) → ℕ) : MP ℤ (m + 1) n ⟶ MP ℤ m (Fin.tail n) :=
  pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))

theorem residueFieldMap_ptCoord_sndM {n : Fin (m + 2) → ℕ} (x : MP ℤ (m + 1) n) (k : Fin (m + 1))
    (j : Bk (Fin.tail n) k) :
    ((sndM m n).residueFieldMap x).hom (ptCoord (sndM m n x) ⟨k, j⟩) = ptCoord x ⟨k.succ, j⟩ :=
  eval_pullRatio_comp (sndM m n) (prB (Fin.tail n) k) x (ptChart (sndM m n x) k) (mem_ptChart (sndM m n x) k) j

theorem closure_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n),
    Subfield.closure (Set.range (ptCoord x)) = ⊤
  | 0, n, x => by
    haveI : IsOpenImmersion (prB n 0) := inferInstanceAs (IsOpenImmersion (𝟙 _))
    refine eq_top_iff.2 fun a _ => range_prB_le x 0 ?_
    exact (ConcreteCategory.bijective_of_isIso ((prB n 0).residueFieldMap x)).2 a
  | m + 1, n, x => by
    have H : Subfield.closure (Set.range ((prB n 0).residueFieldMap x).hom ∪
        Set.range ((sndM m n).residueFieldMap x).hom) = ⊤ :=
      GlobalTheory.closure_range_residueFieldMap_pullback_eq_top _ _ _ (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) x
    rw [eq_top_iff, ← H]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact range_prB_le x 0 ⟨a, rfl⟩
    · rintro _ ⟨a, rfl⟩
      have ha : a ∈ Subfield.closure (Set.range (ptCoord (sndM m n x))) := by
        rw [closure_ptCoord m (Fin.tail n) (sndM m n x)]
        exact Subfield.mem_top a
      have h1 : ((sndM m n).residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
      rw [RingHom.map_field_closure] at h1
      refine Subfield.closure_mono ?_ h1
      rintro _ ⟨_, ⟨⟨k, j⟩, rfl⟩, rfl⟩
      exact ⟨⟨k.succ, j⟩, (residueFieldMap_ptCoord_sndM x k j).symm⟩

theorem blockFnField_ptCoord (x : MP ℤ m n) [CharZero ((MP ℤ m n).residueField x)] :
    blockFnField (ptCoord x) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  have hle : Subfield.closure (Set.range (ptCoord x)) ≤ (blockFnField (ptCoord x)).toSubfield := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨p, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, ?_⟩
    rw [ptCoord_ptChart, div_one]
  exact hle (by rw [closure_ptCoord]; exact Subfield.mem_top a)

theorem blockFnField_comp {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω Ω' : Type*} [Field Ω]
    [CharZero Ω] [Field Ω'] [CharZero Ω'] (g : Ω →ₐ[ℚ] Ω') (y : (Σ k, ι k) → Ω) :
    blockFnField (g ∘ y) = (blockFnField y).map g := by
  unfold blockFnField
  rw [IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp [map_div₀]⟩
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp [map_div₀]⟩

theorem ptCoord_sv (n' : ℕ) {m : ℕ} (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (p : Σ k, Bk n k) :
    ptCoord x (sv n' n p) = ((qpSnd n' m n).residueFieldMap x).hom (ptCoord ((qpSnd n' m n) x) p) :=
  (residueFieldMap_ptCoord_sndM (n := consN n' n) x p.1 p.2).symm

theorem relfinrank_blockFnField_sv : ∀ (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)],
    IntermediateField.relfinrank (blockFnField (ptCoord x ∘ sv n' n)) (blockFnField (ptCoord x)) =
      (qpSnd n' m n).residueDegree x := by
  intro n' m n x _
  let f : (MP ℤ m n).residueField ((qpSnd n' m n) x) ⟶ (MP ℤ (m + 1) (consN n' n)).residueField x :=
    (qpSnd n' m n).residueFieldMap x
  haveI : CharZero ((MP ℤ m n).residueField ((qpSnd n' m n) x)) :=
    (RingHom.charZero_iff f.hom.injective).2 inferInstance
  let g := f.hom.toRatAlgHom
  have e : ptCoord x ∘ sv n' n = g ∘ ptCoord ((qpSnd n' m n) x) := _root_.funext fun p => ptCoord_sv n' n x p
  rw [e, blockFnField_comp, blockFnField_ptCoord, blockFnField_ptCoord, IntermediateField.relfinrank_top_right]
  letI := f.hom.toAlgebra
  let i := (IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ g)).toRingEquiv
  refine (Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) ?_).symm
  ext a
  rfl

end GlobalTheory.CompanionTheory.MPDict.FnDeg
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM =====
