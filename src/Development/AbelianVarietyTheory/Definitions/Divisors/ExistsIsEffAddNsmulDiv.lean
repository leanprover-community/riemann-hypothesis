module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple, Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.Morphisms.Flat\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens\npublic import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp\npublic import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite\npublic import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Amp

variable {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}

end Amp

section Refl

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}

end Refl

section Abelian

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

variable (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)

end Abelian

end GlobalTheory.Models

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange\npublic import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint\npublic import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp\npublic import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.KrullDimension.Polynomial\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.TypeStar\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso\n\n"}
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)

namespace GlobalTheory.Vert

section Divisor

variable {X : Scheme.{0}}

def divMod (I : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (structureModule I.subscheme)

variable (D D' : EffCartierData X)

instance mono_cutHom_canonical : Mono (cutHom (structureModule X) D.isLB_lb D.canonical) :=
  mono_of_locally_app_injective _ fun W x hx =>
    have ⟨i, hi⟩ := D.exists_mem x
    ⟨W ⊓ D.U i, ⟨hx, hi⟩, inf_le_left,
      ((isMulBy_cutHom _ D.isLB_lb D.canonical).injective_app_iff i inf_le_right).2
        fun _ _ h => (mul_cancel_left_mem_nonZeroDivisors (D.regular i _ inf_le_right)).1 h⟩

instance isFiniteQC_divMod : IsFiniteQC (divMod D.idealSheaf) :=
  (nonempty_cut_iso D).elim fun e => .of_iso e

end Divisor

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

structure Model (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] where

  X : Scheme.{0}

  str : X ⟶ Sp O

  [isIntegral : IsIntegral X]

  isProjOver : IsProjOver str

  [flat : Flat str]

attribute [instance] Model.isIntegral Model.flat

namespace Model

variable {O} (Z Z₁ Z₂ : Model O)

instance algebraTop : Algebra O Γ(Z.X, ⊤) := algebraΓOfHom Z.str

abbrev const (g : O) : Γ(Z.X, ⊤) := algebraMap O Γ(Z.X, ⊤) g

instance isNoetherian : AlgebraicGeometry.IsNoetherian Z.X :=
  isNoetherian_of_isProjOver Z.isProjOver

instance isProper : IsProper Z.str := (isProper_and_exists_isAmpleLB_of_isProjOver Z.isProjOver).1

def gen : Z.X.Opens :=
  Z.str ⁻¹ᵁ ⟨{closedPoint O}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint O).isOpen_compl⟩

def relDim : ℕ := Z.exists_dim_eq.choose

variable (O) in
def projSpace (N : ℕ) : Model O where
  X := PSpace O N
  str := PSpace.str O N
  isIntegral := ProjSpace.isIntegral_of_isDomain O N
  isProjOver := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  flat := Models.flat_projSpace O N

structure Hom (Z₁ Z : Model O) where

  f : Z₁.X ⟶ Z.X

  comp_str : f ≫ Z.str = Z₁.str

  [surjective : Surjective f]

attribute [instance] Hom.surjective

def IsVertical (F : Z.X.Modules) : Prop := ∀ x ∈ support F, x ∉ Z.gen

variable {Z} {F G : Z.X.Modules}

def IsVertical.deg [IsFiniteQC F] (h : Z.IsVertical F) : PicSym Z.X →ₗ[ℚ] ℚ := picForm h.diffVanish

end Model

namespace Model

variable {O} (Z Z₁ : Model O)

def effVert : Submonoid Z.X.IdealSheafData where
  carrier := {I | FinalTheorems.EffCartier I ∧ ∀ x ∈ I.support, x ∉ Z.gen}
  one_mem' := ⟨(EffCartierData.idealSheaf_zero (X := Z.X)).subst
    (EffCartierData.zero _).effCartier_idealSheaf, fun x hx => by
      rw [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at hx
      exact hx.elim⟩
  mul_mem' := fun {I J} hI hJ => by
    obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI.1
    obtain ⟨D', rfl⟩ := EffCartierData.exists_idealSheaf_eq hJ.1
    exact ⟨D.idealSheaf_add D' ▸ (D.add D').effCartier_idealSheaf,
      fun x hx => Or.elim hx (hI.2 x) (hJ.2 x)⟩

variable {Z}

def effData (I : Z.effVert) : EffCartierData Z.X :=
  (EffCartierData.exists_idealSheaf_eq I.2.1).choose

def effMk (D : EffCartierData Z.X) (h : ∀ i, Z.gen ⊓ D.U i ≤ Z.X.basicOpen (D.f i)) : Z.effVert :=
  ⟨D.idealSheaf, D.effCartier_idealSheaf, fun x hx hg =>
    have ⟨i, hi⟩ := D.exists_mem x
    (D.mem_support_iff i hi).1 hx (h i ⟨hg, hi⟩)⟩

instance : IsCancelMul Z.effVert :=
  have : IsLeftCancelMul Z.effVert := ⟨fun E D D' h => Subtype.ext <| by
    rw [← idealSheaf_effData, ← idealSheaf_effData]
    refine idealSheaf_mul_left_cancel (E := effData E) ?_
    simp only [idealSheaf_effData]
    exact congrArg Subtype.val h⟩
  CommMagma.IsLeftCancelMul.toIsCancelMul _

instance (I : Z.effVert) : IsFiniteQC (divMod I.1) := idealSheaf_effData I ▸ isFiniteQC_divMod _

def effCls (I : Z.effVert) : Pic Z.X := cls _ (effData I).isLB_lb

def effDeg (I : Z.effVert) : PicSym Z.X →ₗ[ℚ] ℚ := (isVertical_divMod I).deg

variable (Z) in
abbrev VDivZ : Type := Algebra.GrothendieckAddGroup (Additive Z.effVert)

def ofEff (I : Z.effVert) : Z.VDivZ := Algebra.GrothendieckAddGroup.of (Additive.ofMul I)

def vLift {A : Type*} [AddCommGroup A] (f : Z.effVert → A) (h : ∀ I J, f (I * J) = f I + f J) :
    Z.VDivZ →+ A :=
  Algebra.GrothendieckAddGroup.lift (AddMonoidHom.mk' (fun I => f I.toMul) h)

variable (Z)

def vCls : Z.VDivZ →+ Pic Z.X := vLift effCls effCls_mul

def vDeg : Z.VDivZ →+ (PicSym Z.X →ₗ[ℚ] ℚ) := vLift effDeg effDeg_mul

def effConst (g : O) (hg : g ≠ 0) : Z.effVert :=
  effMk (.principal (Z.const g) (Z.isRegularFn_const hg))
    fun _ => inf_le_left.trans (Z.gen_le_basicOpen hg)

def div (g : O) (hg : g ≠ 0) : Z.VDivZ := ofEff (Z.effConst g hg)

section Pull

variable {Z Z₁} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
include hf

def effPull (I : Z.effVert) : Z₁.effVert :=
  ⟨I.1.comap f, idealSheaf_effData I ▸ ((effData I).keepsRegular_iff_effCartier f).1
    (keepsRegular hf (idealSheaf_effData I)), fun x hx h => by
      rw [Scheme.IdealSheafData.support_comap] at hx
      exact I.2.2 _ hx ((preimage_gen hf).ge h)⟩

def vPull : Z.VDivZ →+ Z₁.VDivZ :=
  vLift (fun I => ofEff (effPull hf I)) fun I J => by rw [effPull_mul, ofEff_mul]

end Pull

end Model

variable {O} in
structure VertDiv (Z : Model O) where

  M : LB Z.X

  isLB : M.IsLB

  t : Γ(toMod M, Z.gen)

  isUnit : ∀ i, IsUnit (coord t i)

namespace VertDiv

open Model

variable {O} {Z : Model O} (P P' P'' : VertDiv Z)

def eqn (i : P.M.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) : Γ(Z.X, W) :=
  resG Z.X h (coord P.t i)

def ofUnits (M : LB Z.X) (hM : M.IsLB) (u : ∀ i, Γ(Z.X, Z.gen ⊓ M.U i))
    (hu : ∀ i, IsUnit (u i)) (h : u ∈ secOn M Z.gen) : VertDiv Z :=
  ⟨M, hM, LB.mkSec u h, hu⟩

variable (Z) in
def zero : VertDiv Z :=
  ofUnits (LB.triv _) (LB.isLB_triv _) (fun _ => 1) (fun _ => isUnit_one) fun _ _ => by
    change _ = resG Z.X _ 1 * _
    simp only [map_one, mul_one]

variable (Z) in
def const (g : O) (hg : g ≠ 0) : VertDiv Z :=
  ofUnits (LB.triv _) (LB.isLB_triv _) (fun _ => resG Z.X le_top (Z.const g))
    (fun _ => Z.isUnit_const hg inf_le_left) fun _ _ => by
      change _ = resG Z.X _ 1 * _
      simp only [map_one, one_mul, resG_resG]

def add : VertDiv Z :=
  ofUnits (tens P.M P'.M) (isLB_tens P.isLB P'.isLB)
    (fun p => P.eqn p.1 (inf_le_inf_left _ inf_le_left) * P'.eqn p.2 (inf_le_inf_left _ inf_le_right))
    (fun _ => (P.isUnit_eqn _ _).mul (P'.isUnit_eqn _ _)) fun p q => by
      simp only [map_mul, resG_eqn]
      exact eqn_mul_rel P P' p.1 q.1 p.2 q.2 _ _ _ _ _ _ _

def ofEff (I : Z.effVert) : VertDiv Z :=
  ⟨(effData I).lb, (effData I).isLB_lb, ofSec (effData I).canonical _, fun i => by
    refine (resG_resG (Z.X.basicOpen_le ((effData I).f i)) (le_basicOpen_effData I i) _).subst ?_
    exact (Z.X.toRingedSpace.isUnit_res_basicOpen _).map _⟩

def IsIsom : Prop := ∃ w : LB.Iso P.M P'.M, w.IsGen ∧ ∀ (p : P'.M.ι) (q : P.M.ι),
  P'.eqn p (inf_le_inf_left _ inf_le_left : Z.gen ⊓ (P'.M.U p ⊓ P.M.U q) ≤ _) =
    resG Z.X inf_le_right (Twist.isoUnit w p q : Γ(Z.X, P'.M.U p ⊓ P.M.U q)) *
      P.eqn q (inf_le_inf_left _ inf_le_right)

def Extends (g : O) (s : P.M.Sec) : Prop :=
  ofSec s Z.gen = resG Z.X (le_top : Z.gen ≤ ⊤) (Z.const g) • P.t

variable {P P' P''} {g g' g'' : O} {s : P.M.Sec} {s' : P'.M.Sec} {s'' : P''.M.Sec}

def Extends.eff (h : P.Extends g s) (hg : g ≠ 0) : Z.effVert :=
  effMk (.ofSec P.isLB s (h.isRegularSec hg)) (h.le_basicOpen hg)

variable (P P' P'') in
def IsSum : Prop := ∀ (i : P.M.ι) (j : P'.M.ι) (k : P''.M.ι),
  ∃ u : Γ(Z.X, P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k)ˣ,
    P''.eqn k (inf_le_inf_left _ inf_le_right : Z.gen ⊓ (P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k) ≤ _) =
      resG Z.X inf_le_right u * (P.eqn i (inf_le_inf_left _ (inf_le_left.trans inf_le_left)) *
        P'.eqn j (inf_le_inf_left _ (inf_le_left.trans inf_le_right)))

variable (P) in
def cls : Z.VDivZ :=
  Model.ofEff (P.exists_extends'.choose_spec.eff P.exists_extends'.choose.1.2) -
    Z.div _ P.exists_extends'.choose.1.2

section Pull

variable {Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)

end Pull

end VertDiv

namespace Model

variable {O} {Z : Model O}

end Model

end GlobalTheory.Vert
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv =====
