module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumLeftPull
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInclusionFirstFactorOverAbelianInclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumInsertKilledCoordinateComp
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactor, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivial, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastExtra, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK, Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIso, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPair

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactor =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactor", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumLeftPull\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.CubeIso

section

variable {X X₁ X₂ Y : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

theorem mem_ext {x : X} {j₁ : L₁.ι} {j₂ : L₂.ι} (h₁ : f₁ x ∈ L₁.U j₁) (h₂ : f₂ x ∈ L₂.U j₂) :
    x ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) :=
  ⟨mem_pull.2 h₁, mem_pull.2 h₂⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂') :
    gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
        (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂'))
      ((extLB L₁ L₂ f₁ f₂).g (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂')) =
      gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') * gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') := by
  have hm : r z ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
      (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂') := ⟨mem_ext h₁ h₂, mem_ext h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hm _).trans ?_) ((gm_res r z _ hm _).trans ?_))
  · exact gm_pull_g L₁ f₁ r z (fun _ => j₁) (fun _ => j₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g L₂ f₂ r z (fun _ => j₂) (fun _ => j₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

def ev (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι) (k : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓ L.U k)
    (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k))

theorem ev_trans {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z)
    (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι) (k k' : L.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂')
    (h : r z ∈ L.U k) (h' : r z ∈ L.U k') :
    ev w r z j₁ j₂ k = gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') *
      gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') * (gm r z (L.U k ⊓ L.U k') (L.g k k'))⁻¹ *
        ev w r z j₁' j₂' k' := by
  rw [← gm_ext_g r z j₁ j₁' j₂ j₂' h₁ h₁' h₂ h₂']
  exact AdjComp.gm_iso hw r z (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂', k')
    ⟨mem_ext h₁ h₂, h⟩ ⟨mem_ext h₁' h₂', h'⟩

theorem exists_linComb (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (w₀ : LB.Iso L (extLB L₁ L₂ f₁ f₂))
    (hw₀ : w₀.IsGen) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ₁ : K → (Y ⟶ X₁)) (ε : K → ℤ) (σ : K → K)
    (h₁ : ∀ k, φ k ≫ f₁ = φ₁ k) (h₂ : ∀ k, φ k ≫ f₂ = φ (σ k) ≫ f₂)
    (hε : ∀ (G : Type) [CommGroup G] (a : K → G), (∀ k, a k = a (σ k)) → ∏ k, a k ^ ε k = 1) :
    ∃ w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L₁ φ₁ ε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (jC : K → L₁.ι) (jA : K → L.ι) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ φ₁ jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) →
        gm f z (LB.wchart L₁ φ₁ jC ⊓ LB.wchart L φ jA) (w.s (jC, jA)) =
          ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
  obtain rfl : (fun k => φ k ≫ f₁) = φ₁ := funext h₁
  have cover : ∀ y : Y, ∃ β : K → L₂.ι, (∀ k, f₂ (φ k y) ∈ L₂.U (β k)) ∧ ∀ k, β k = β (σ k) := fun y => by
    choose c hc using exists_chart hL₂
    exact ⟨fun k => c ((φ k ≫ f₂) y), fun k => hc _, fun k => congrArg (fun q : Y ⟶ X₂ => c (q y)) (h₂ k)⟩
  have glue : ∀ (jC : K → L₁.ι) (jA : K → L.ι),
      ∃ s : Γ(Y, LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ (fun k => φ k ≫ f₁) jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) → gm f z _ s = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
    intro jC jA
    let W : {β : K → L₂.ι // ∀ k, β k = β (σ k)} → Y.Opens := fun β =>
      LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA ⊓ LB.wchart L₂ (fun k => φ k ≫ f₂) β.1
    have l₀ : ∀ β, W β ≤ LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA := fun β => inf_le_left
    have l₁ : ∀ β k, W β ≤ φ k ⁻¹ᵁ
        ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k)) ⊓ L.U (jA k)) := fun β k y hy =>
      ⟨mem_ext (Set.mem_iInter.1 hy.1.1 k) (Set.mem_iInter.1 hy.2 k), Set.mem_iInter.1 hy.1.2 k⟩
    let u : ∀ β, Γ(Y, W β)ˣ := fun β => ∏ k, res (l₁ β k)
      (pullU (φ k) _ (w₀.s (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k), jA k))) ^ ε k
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) β (hz : f z ∈ W β),
        gm f z (W β) (u β) = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β.1 k) (jA k) ^ ε k := fun Z f z β hz =>
      (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
        ((gm_res f z (l₁ β k) hz _).trans (gm_pull f (φ k) z _ (l₁ β k hz) _))))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun y hy => by
        obtain ⟨β, hβ, hβ'⟩ := cover y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨β, hβ'⟩, hy, Set.mem_iInter.2 hβ⟩) u (fun β β' y hy => by
        rw [hu _ (𝟙 Y) y β hy.1, hu _ (𝟙 Y) y β' hy.2]
        have a : ∀ k, ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β.1 k) (jA k) =
            gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k)) *
              ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β'.1 k) (jA k) := fun k => by
          have m₁ : f₁ (φ k y) ∈ L₁.U (jC k) := Set.mem_iInter.1 hy.1.1.1 k
          have m : φ k y ∈ L.U (jA k) := Set.mem_iInter.1 hy.1.1.2 k
          rw [Category.id_comp, ev_trans hw₀ (φ k) y (jC k) (jC k) (β.1 k) (β'.1 k) (jA k) (jA k) m₁ m₁
            (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k) m m, gm_self hL₁ (φ k ≫ f₁) y m₁,
            gm_self hL (φ k) y m, _root_.one_mul, inv_one, _root_.mul_one]
        simp only [a, mul_zpow, Finset.prod_mul_distrib]
        rw [hε _ (fun k => gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k))) (fun k => by
          have key : ∀ (q q' : Y ⟶ X₂) (i i' j j' : L₂.ι), q = q' → i = i' → j = j' →
              gm q y (L₂.U i ⊓ L₂.U j) (L₂.g i j) = gm q' y (L₂.U i' ⊓ L₂.U j') (L₂.g i' j') := by
            rintro _ _ _ _ _ _ rfl rfl rfl; rfl
          exact key _ _ _ _ _ _ (h₂ k) (β.2 k) (β'.2 k)), _root_.one_mul])
    refine ⟨s, fun Z f z β hC hA hβ hβ' => ?_⟩
    have hy : f z ∈ W ⟨β, hβ'⟩ := ⟨⟨hC, hA⟩, Set.mem_iInter.2 hβ⟩
    exact (gm_res f z (l₀ ⟨β, hβ'⟩) hy s).symm.trans
      ((congrArg (gm f z (W ⟨β, hβ'⟩)) (hs ⟨β, hβ'⟩)).trans (hu Z f z ⟨β, hβ'⟩ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun i j => unit_ext fun y hy => ?_,
    fun Z f z jC jA β hC hA hβ hβ' => hs jC jA Z f z β hC hA hβ hβ'⟩
  obtain ⟨β, hβ, hβ'⟩ := cover y
  have e₁ := hs i.1 i.2 _ (𝟙 Y) y β hy.1.1 hy.1.2 hβ hβ'
  have e₂ := hs j.1 j.2 _ (𝟙 Y) y β hy.2.1 hy.2.2 hβ hβ'
  have gC := gm_linComb L₁ (fun k => φ k ≫ f₁) ε (𝟙 Y) y i.1 j.1 hy.1.1 hy.2.1
  have gA := gm_linComb L φ ε (𝟙 Y) y i.2 j.2 hy.1.2 hy.2.2
  refine (gm_res (𝟙 Y) y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) ((gm_div (LB.LinComb L φ ε) (LB.LinComb L₁ (fun k => φ k ≫ f₁) ε) (𝟙 Y) y i j hy).trans
    (congrArg₂ (fun a b => a * b⁻¹) gC gA)) ((gm_res (𝟙 Y) y _ hy _).trans e₂)).trans ?_
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Category.id_comp]
  rw [ev_trans hw₀ (φ k) y (i.1 k) (j.1 k) (β k) (β k) (i.2 k) (j.2 k) (Set.mem_iInter.1 hy.1.1 k)
    (Set.mem_iInter.1 hy.2.1 k) (hβ k) (hβ k) (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k),
    gm_self hL₂ (φ k ≫ f₂) y (hβ k), _root_.mul_one, mul_zpow, mul_zpow, inv_zpow]

end

theorem cancel_two (G : Type) [CommGroup G] (a : ULift.{0} (Finset (Fin 2)) → G)
    (h : ∀ I, a I = a ⟨insert 0 I.down⟩) : ∏ I, a I ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  rw [← Equiv.prod_comp (Equiv.ulift.{0}.symm : Finset (Fin 2) ≃ ULift.{0} (Finset (Fin 2)))]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have e₀ : a ⟨∅⟩ = a ⟨{0}⟩ := h ⟨∅⟩
  have e₁ : a ⟨{1}⟩ = a ⟨{0, 1}⟩ := h ⟨{1}⟩
  show a ⟨∅⟩ ^ (1 : ℤ) * (a ⟨{0}⟩ ^ (-1 : ℤ) * (a ⟨{1}⟩ ^ (-1 : ℤ) * a ⟨{0, 1}⟩ ^ (1 : ℤ))) = 1
  rw [e₀, e₁]
  simp

end GlobalTheory.MumProd.CubeIso

namespace GlobalTheory.MumProd

theorem exists_cubeIso : ∀ (S : Scheme.{0}) (B B₁ B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B₂] [IsCommMonObj B₂] (M : LB B.left) (M₁ : LB B₁.left) (M₂ : LB B₂.left), M.IsLB → M₁.IsLB → M₂.IsLB → ∀ (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (wM : LB.Iso M (extLB M₁ M₂ p₁.left p₂.left)), wM.IsGen → ∀ (x : Fin 2 → (T ⟶ B)) (x₁ : Fin 2 → (T ⟶ B₁)), (∀ I : Finset (Fin 2), psum B x I ≫ p₁ = psum B₁ x₁ I) → (∀ I : Finset (Fin 2), psum B x I ≫ p₂ = psum B x (insert 0 I) ≫ p₂) → ∃ w : LB.Iso (cubeLB B x M) (cubeLB B₁ x₁ M₁), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ T.left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → M₁.ι) (jA : ULift.{0} (Finset (Fin 2)) → M.ι) (β : ULift.{0} (Finset (Fin 2)) → M₂.ι), f z ∈ (cubeLB B₁ x₁ M₁).U jC → f z ∈ (cubeLB B x M).U jA → (∀ I, (f ≫ (psum B x I.down).left ≫ p₂.left) z ∈ M₂.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum B x I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  intro S B B₁ B₂ T _ _ _ _ _ _ M M₁ M₂ hM hM₁ hM₂ p₁ p₂ wM hwM x x₁ h₁ h₂
  obtain ⟨w, hw, H⟩ := CubeIso.exists_linComb hM hM₁ hM₂ wM hwM (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B x I.down).left) (fun I => (psum B₁ x₁ I.down).left) (fun I => (-1) ^ (2 - I.down.card))
    (fun I => ⟨insert 0 I.down⟩) (fun I => by rw [← Over.comp_left, h₁])
    (fun I => by rw [← Over.comp_left, ← Over.comp_left, h₂]) CubeIso.cancel_two
  exact ⟨w, hw, fun Z f z jC jA β hC hA hβ hβ' => H Z f z jC jA β hC hA hβ hβ'⟩

end GlobalTheory.MumProd
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactor =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivial =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivial", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.Pullbacks\npublic import Mathlib.Combinatorics.Quiver.ReflQuiver\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory

theorem isMonHom_section_of_prod_trivial :
    ∀ (S : Scheme.{0}) (B B₁ B₂ : Over S) [GrpObj B] [GrpObj B₁] [GrpObj B₂] (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (i₁ : B₁ ⟶ B), IsMonHom p₁ → IsMonHom p₂ → IsIso (lift p₁ p₂) → i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[B₂] → IsMonHom i₁ := by
  intro S B B₁ B₂ _ _ _ p₁ p₂ i₁ h₁ h₂ hiso hi₁ hi₂
  have key : ∀ {X : Over S} (f g : X ⟶ B), f ≫ p₁ = g ≫ p₁ → f ≫ p₂ = g ≫ p₂ → f = g := by
    intro X f g e₁ e₂
    rw [← cancel_mono (lift p₁ p₂)]
    ext <;> simp [e₁, e₂]
  constructor
  · apply key
    · simp [hi₁]
    · simp only [Category.assoc, hi₂, IsMonHom.one_hom]
  · apply key
    · simp only [Category.assoc, hi₁, IsMonHom.mul_hom, Category.comp_id]
      rw [tensorHom_comp_tensorHom_assoc, hi₁, tensorHom_id, id_whiskerRight, Category.id_comp]
    · simp only [Category.assoc, hi₂, IsMonHom.mul_hom]
      rw [tensorHom_comp_tensorHom_assoc, hi₂]

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivial =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastExtra =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastExtra", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem mapsAt₂_val : ∀ (Y X X₁ X₂ Z : Scheme.{0}) (L : LB X) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ) (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))) (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))), MapsAt₂ w p n a b₁ b₂ → ∀ (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι), Good L z J → Good L₁ z J₁ → Good L₂ z J₂ → val b₁ r z J₁ * val b₂ r z J₂ = gm (r ≫ p) z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)), J (r ≫ p))) ^ n * val a r z J := by
  intro Y X X₁ X₂ Z L L₁ L₂ f₁ f₂ w p n a b₁ b₂ hM r z J J₁ J₂ hJ hJ₁ hJ₂
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U
      (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)), J (r ≫ p)) :=
    ⟨⟨Set.mem_iInter.2 fun _ => hJ₁ (r ≫ p ≫ f₁), Set.mem_iInter.2 fun _ => hJ₂ (r ≫ p ≫ f₂)⟩, hJ (r ≫ p)⟩
  have e := congrArg (gm r z _) (hM (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)) (J (r ≫ p)))
  rw [map_mul, map_mul, map_zpow] at e
  exact (congrArg₂ (· * ·) (gm_res r z _ hm _) (gm_res r z _ hm _)).symm.trans
    (e.trans (congrArg₂ (· * ·) (congrArg (· ^ n) (gm_pull r p z _ hm _)) (gm_res r z _ hm _)))

end GlobalTheory.MumProd
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastExtra =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumFam

theorem val_psi_zero_mul_rigK : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi 0) (𝟙 _) z J * val D.rigK (𝟙 _) z J = 1 := by
  intro R _ _ D hB z J hJ
  have h1 := GlobalTheory.PolDeg.Data.val_tau_zero (GlobalTheory.PolDeg.Wit.ofDeg D hB) 0 z J hJ
  have h2 : val ((GlobalTheory.PolDeg.Wit.ofDeg D hB).tau 0 0) (𝟙 _) z J = val (D.tau 0 0) (𝟙 _) z J :=
    (GlobalTheory.PolDeg.Wit.exists_tau D 0 0).choose_spec.2 _ _ z J hJ
  rw [h2] at h1
  unfold DegPre.tau at h1
  rw [val_mul hJ, val_mul hJ, val_mul hJ] at h1
  simp only [val_inv] at h1
  rw [congrArg (fun w => val (D.psi w) (𝟙 _) z J) (add_zero (0 : D.X)), mul_inv_cancel, _root_.one_mul,
    ← mul_inv_rev, inv_eq_one] at h1
  rw [mul_comm]
  exact h1

end GlobalTheory.MumFam
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIso =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIso", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastExtra\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInclusionFirstFactorOverAbelianInclusion\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumInsertKilledCoordinateComp\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValPsiZeroMulRigK\npublic import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculus\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SumTau

theorem prod_subsets_two {M : Type} [CommMonoid M] (F : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{0, 1}⟩ := by
  have h : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, _root_.mul_assoc, _root_.mul_assoc]

def unitAt {X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι)
    (J₂ : (Z ⟶ X₂) → L₂.ι) (f : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm f z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (f ≫ f₁)) (J₂ (f ≫ f₂)), J f))

theorem unitAt_of {X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι)
    (J₂ : (Z ⟶ X₂) → L₂.ι) (f g : Z ⟶ X) (j : L.ι) (j₁ : L₁.ι) (j₂ : L₂.ι) (hg : g = f) (h : J f = j)
    (h₁ : J₁ (f ≫ f₁) = j₁) (h₂ : J₂ (f ≫ f₂) = j₂) :
    gm g z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, j)) = unitAt w z J J₁ J₂ f := by
  subst hg h h₁ h₂
  rfl

theorem mapsAt_unitAt {Y X X₁ X₂ Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} {p : Y ⟶ X} {n : ℤ}
    {a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    {b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))}
    {b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))} (h : MapsAt₂ w p n a b₁ b₂)
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} {J₁ : (Z ⟶ X₁) → L₁.ι} {J₂ : (Z ⟶ X₂) → L₂.ι}
    (hJ : Good L z J) (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    val b₁ r z J₁ * val b₂ r z J₂ = unitAt w z J J₁ J₂ (r ≫ p) ^ n * val a r z J :=
  (GlobalTheory.MumProd.mapsAt₂_val _ _ _ _ _ _ _ _ _ _ w p n a b₁ b₂ h r z J J₁ J₂ hJ hJ₁ hJ₂).trans
    (congrArg (· ^ n * val a r z J) (unitAt_of w z J J₁ J₂ _ _ _ _ _ rfl rfl
      (by rw [Category.assoc]) (by rw [Category.assoc])))

theorem val_tau {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) (a b : D.toPre.X)
    {z : (TK R).left} {J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} (hJ : Good D.toPre.P.L z J) :
    val ((pol D).tau a b) (𝟙 _) z J = val (D.toPre.psi (a + b)) (𝟙 _) z J * (val (D.toPre.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.toPre.psi b) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ := by
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre a b).choose_spec.2 _ (𝟙 _) z J hJ).trans ?_
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

section Psum

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Over S} (x : Fin 2 → (T ⟶ G))

theorem psum_empty : psum G x ∅ = toUnit T ≫ η[G] := rfl

theorem psum_zero : psum G x {0} = x 0 := by
  show lift (x 0) (toUnit T ≫ η[G]) ≫ μ[G] = x 0
  exact lift_comp_one_right _ _

theorem psum_one : psum G x {1} = x 1 := by
  show lift (x 1) (toUnit T ≫ η[G]) ≫ μ[G] = x 1
  exact lift_comp_one_right _ _

theorem psum_pair : psum G x {0, 1} = padd G (x 0) (x 1) := by
  show padd G (x 0) (lift (x 1) (toUnit T ≫ η[G]) ≫ μ[G]) = _
  rw [lift_comp_one_right]

alias comp_padd' := _root_.ReciprocityTheory.ChartRestriction.G.Out.CubePf.comp_padd'

end Psum

end GlobalTheory.MumProd.SumTau

namespace GlobalTheory.MumProd


open SumTau in
theorem tau_sum_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)), wM.IsGen → (∃ b₁ b₂, MapsAt₂ wM (eSec D.toPre.P.A) 1 D.toPre.rig b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ D₁.toPre.rig ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ D₂.toPre.rig) → (∀ x, ∃ b₁ b₂, MapsAt₂ wM (D.toPre.xK x) (-1) (D.toPre.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ (D₁.toPre.psi (q₁ x)) ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ (D₂.toPre.psi (q₂ x))) → ∀ (w : LB.Iso (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L) (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L)), (∀ (Z : Scheme.{0}) (f : Z ⟶ (D₁.toPre.P.A ⊗ D.toPre.P.A).left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → D₁.toPre.P.L.ι) (jA : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι) (β : ULift.{0} (Finset (Fin 2)) → D₂.toPre.P.L.ι), f z ∈ (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L).U jC → f z ∈ (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L).U jA → (∀ I, (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left) z ∈ D₂.toPre.P.L.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card))) → ∀ (y : D₁.toPre.X) (y' : D.toPre.X) (z : (TK R).left) (J₁ : ((TK R).left ⟶ D₁.toPre.P.A.left) → D₁.toPre.P.L.ι) (J₂ : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D₁.toPre.P.L z J₁ → Good D.toPre.P.L z J₂ → val ((pol D).tau (j₁ y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ * val ((pol D₁).tau y (q₁ y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ hi₁ hi₂ hj₁ hj₂ wM _ hrig hpsi w hw y y' z J₁ J₂ hJ₁ hJ₂
  obtain ⟨J₃, hJ₃⟩ := GlobalTheory.ChartCmp.CarryCalc.exists_good' D₂.toPre.P.isLB z
  have ψ : ∀ x, val (D₁.toPre.psi (q₁ x)) (𝟙 _) z J₁ * val (D₂.toPre.psi (q₂ x)) (𝟙 _) z J₃ =
      (unitAt wM z J₂ J₁ J₃ (D.toPre.xK x))⁻¹ * val (D.toPre.psi x) (𝟙 _) z J₂ := by
    intro x
    obtain ⟨b₁, b₂, hm, c₁, c₂⟩ := hpsi x
    have e := mapsAt_unitAt hm (𝟙 _) hJ₂ hJ₁ hJ₃
    rw [val_corr hJ₁ c₁, val_corr hJ₃ c₂, Category.id_comp, zpow_neg_one] at e
    exact e
  have ρ : val D₁.toPre.rigK (𝟙 _) z J₁ * val D₂.toPre.rigK (𝟙 _) z J₃ =
      unitAt wM z J₂ J₁ J₃ (toUnit (TK R) ≫ η[D.toPre.P.A]).left * val D.toPre.rigK (𝟙 _) z J₂ := by
    obtain ⟨b₁, b₂, hm, c₁, c₂⟩ := hrig
    have e := mapsAt_unitAt hm (toUnit (TK R)).left hJ₂ hJ₁ hJ₃
    rw [val_corr hJ₁ c₁, val_corr hJ₃ c₂, zpow_one] at e
    unfold DegPre.rigK
    rw [val_pull hJ₁, val_pull hJ₃, val_pull hJ₂, Category.id_comp]
    exact e
  have z₂ := GlobalTheory.MumFam.val_psi_zero_mul_rigK R D₂.toPre D₂.tau_bimult z J₃ hJ₃
  have hc := GlobalTheory.MumProd.c_inc_fst R D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ hS i₁ j₁ hi₁ hi₂ hj₁ hj₂ y
  have h1 := GlobalTheory.MumProd.PsumMap.psum_comp_hom _ D.toPre.P.A D₁.toPre.P.A _ 2 p₁
    ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁
    (by intro i; fin_cases i <;> simp [hi₁])
  have h2 := GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ D.toPre.P.A D₂.toPre.P.A _ p₂
    ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by
      show (fst D₁.toPre.P.A D.toPre.P.A ≫ i₁) ≫ p₂ = _
      rw [Category.assoc, hi₂, ← Category.assoc, comp_toUnit])
  have K : adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ =
      unitAt wM z J₂ J₁ J₃ (toUnit (TK R) ≫ η[D.toPre.P.A]).left * (unitAt wM z J₂ J₁ J₃ (D.toPre.xK (j₁ y)))⁻¹ *
        (unitAt wM z J₂ J₁ J₃ (D.toPre.xK y'))⁻¹ * unitAt wM z J₂ J₁ J₃ (D.toPre.xK (j₁ y + y')) := by
    have s₀ : lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') ≫
        fst D₁.toPre.P.A D.toPre.P.A ≫ i₁ = toUnit (TK R) ≫ D.toPre.c (j₁ y) := by
      rw [lift_fst_assoc, hc, Category.assoc]
    have s₁ : lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') ≫
        snd D₁.toPre.P.A D.toPre.P.A = toUnit (TK R) ≫ D.toPre.c y' := lift_snd _ _
    generalize lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y') = P at s₀ s₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift.{0} (Finset (Fin 2)) => (psum D₁.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] I.down).left) P.left
    have mA := Good.mem hJ₂ (fun I : ULift.{0} (Finset (Fin 2)) => (psum D.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) P.left
    have e := hw _ P.left z _ _ (fun I => J₃ (P.left ≫ (psum D.toPre.P.A
      ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left)) mC mA
      (fun I => hJ₃ _) (fun I => by
        show J₃ _ = J₃ _
        rw [← Over.comp_left, ← Over.comp_left, h2 I.down]
        rfl)
    refine e.trans ?_
    have e' : ∀ I : ULift.{0} (Finset (Fin 2)), gm (P.left ≫ (psum D.toPre.P.A
        ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _
        (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (J₁ (P.left ≫ (psum D₁.toPre.P.A
          ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] I.down).left))
          (J₃ (P.left ≫ (psum D.toPre.P.A
            ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left)),
          J₂ (P.left ≫ (psum D.toPre.P.A
            ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left))) =
        unitAt wM z J₂ J₁ J₃ (P ≫ psum D.toPre.P.A
          ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left := fun I =>
      unitAt_of wM z J₂ J₁ J₃ _ _ _ _ _ rfl rfl
        (by rw [← h1 I.down, Over.comp_left, Over.comp_left, Category.assoc])
        (by rw [Over.comp_left, Category.assoc])
    refine (Finset.prod_congr rfl fun I _ => congrArg (· ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e' I)).trans ?_
    rw [prod_subsets_two]
    have t₀ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] ∅ =
        toUnit (TK R) ≫ η[D.toPre.P.A] := by
      rw [psum_empty, ← Category.assoc, comp_toUnit]
    have t₁ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {0} =
        toUnit (TK R) ≫ D.toPre.c (j₁ y) := by
      rw [psum_zero]; exact s₀
    have t₂ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {1} =
        toUnit (TK R) ≫ D.toPre.c y' := by
      rw [SumTau.psum_one]; exact s₁
    have t₃ : P ≫ psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] {0, 1} =
        toUnit (TK R) ≫ D.toPre.c (j₁ y + y') := by
      rw [psum_pair, D.toPre.c_add, comp_padd', comp_padd']
      exact congrArg₂ (padd D.toPre.P.A) s₀ s₁
    have c₀ : ((-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card)) = 1 := by decide
    have c₁ : ((-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card)) = -1 := by decide
    have c₂ : ((-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card)) = -1 := by decide
    have c₃ : ((-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card)) = 1 := by decide
    simp only []
    rw [t₀, t₁, t₂, t₃, c₀, c₁, c₂, c₃, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]
  have ψa := ψ (j₁ y)
  have ψb := ψ y'
  have ψab := ψ (j₁ y + y')
  rw [hj₁, hj₂] at ψa
  rw [map_add (f := _), map_add (f := _), hj₁, hj₂, zero_add] at ψab
  rw [K, val_tau D _ _ hJ₂, val_tau D₁ _ _ hJ₁, ← inv_mul_eq_iff_eq_mul.2 ψa, ← inv_mul_eq_iff_eq_mul.2 ψb,
    ← inv_mul_eq_iff_eq_mul.2 ψab, ← inv_mul_eq_iff_eq_mul.2 ρ, eq_inv_of_mul_eq_one_left z₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumProd
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIso =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPair =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPair", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactor\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivial\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInclusionFirstFactorOverAbelianInclusion\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumInsertKilledCoordinateComp\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIso\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProdAdj

theorem adj_first_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂
  obtain ⟨wM, hwM, hrig, hpsi⟩ := hS.w
  have hi₁ : IsMonHom i₁ := GlobalTheory.isMonHom_section_of_prod_trivial _ _ _ _ p₁ p₂ i₁ hS.hom₁ hS.hom₂ hS.lim e₁ e₂
  have m₁ := GlobalTheory.MumProd.PsumMap.psum_comp_hom _ _ _ _ 2 p₁ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁ (fun i => by
      fin_cases i
      · simp [e₁]
      · simp)
  have m₂ := GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ _ _ _ p₂ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by simp [e₂])
  obtain ⟨w, hw, hval⟩ := GlobalTheory.MumProd.exists_cubeIso _ _ _ _ _ D.toPre.P.L D₁.toPre.P.L D₂.toPre.P.L D.toPre.P.isLB D₁.toPre.P.isLB
    D₂.toPre.P.isLB p₁ p₂ wM hwM _ _ m₁ m₂
  exact ⟨hi₁, hS.hom₁, fun y => GlobalTheory.MumProd.c_inc_fst _ _ _ _ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y, fun z => (hS.c_pr₁ z).symm, w, hw,
    GlobalTheory.MumProd.tau_sum_fst R I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ wM hwM hrig hpsi w hval⟩

end GlobalTheory.MumProdAdj
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPair =====
