module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel, Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

section Fun

variable {O : Type} [CommRing O]

def resInt (O : Type) [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) : InvFun O where
  toFun n B := φ.eval (Fin n → O) B
  inv n m r hr B := φ.eval_comp (r := r.restrictScalars ℤ) hr B
  zero B := by
    rw [φ.eval_eq (n := 0) (r := 0) fun a => ⟨0, Subsingleton.elim _ _⟩]
    exact φ.zero _

def IsTame (φ : InvFun O) : Prop :=
  (∀ (n k : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
    ∀ n B, 0 ≤ φ.toFun n B

end Fun

section Cones

variable {R : Type} [CommRing R] [IsDomain R]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Refines (H : Host E) (q : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) : Prop :=
  IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ IsTwInv H φ ∧ IsPosFn H φ ∧ IsTame φ ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
        (resInt (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ

end Cones

end GlobalTheory.TorRef
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel", "h": "module\n\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral\npublic import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective\n\n"}
section -- clump:auto
@[expose] public section

section ProOpen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.HomExtProOpen

open GlobalTheory GlobalTheory.HomExt GlobalTheory.HomExtNormal

theorem existsUnique_hom_extension_of_dvr
    (H : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f))
    (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (hX : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G G' : Over X) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') (hf : IsMonHom f) :
    ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f :=
  GlobalTheory.HomExtNormal.existsUnique_hom_extension_of_dvr_of_preimmersion
    H X U j hX G G' hG hG' f hf

end GlobalTheory.HomExtProOpen

end ProOpen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory
open scoped CategoryTheory.Obj
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral\nimport Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeGenDesc

theorem exists_iso_of_extensions {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    {A : Over U} [GrpObj A] {G G' : Over X} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A G' j ψ) :
    ∃ e : G ≅ G', IsMonHom e.hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  obtain ⟨a, ha, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G G' hG hG' (a.inv ≫ b.hom) inferInstance
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G' G hG' hG (b.inv ≫ a.hom) inferInstance
  obtain ⟨h₁, h₂⟩ := ExtUnique.comp_eq_id_of_pullback j (a.symm ≪≫ b) F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, hF⟩

theorem lbIso_hodge_pull {S T : Scheme.{0}} {G : Over S} {G' : Over T} [GrpObj G] [GrpObj G'] [QuasiSeparated G.hom]
    {f : T ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega G) g) :
    LBIso ((hodge G g).pull f) (hodge G' g) :=
  (hg.lbIso_det_pullback f).trans (pull_isLB hg.isLB_det f) (hg.pullback f).isLB_det
    (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h hg).isLB_det
    ((hg.pullback f).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase h)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F}

end GlobalTheory.HodgeGenDesc

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso =====
