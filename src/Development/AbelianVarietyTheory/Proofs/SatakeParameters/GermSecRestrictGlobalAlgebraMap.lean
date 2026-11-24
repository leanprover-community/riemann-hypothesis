module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeCoh

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Sp k)

def germSec {V : X.Opens} (hη : genericPoint X ∈ V) : Sec s V →+* X.functionField :=
  (X.presheaf.germ V (genericPoint X) hη).hom

theorem semiHom_germSec {V : X.Opens} (hη : genericPoint X ∈ V) :
    letI := ffAlg s; SemiHom (RingHom.id k) (germSec s hη) := by
  letI := ffAlg s
  intro r b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
  congr 1
  change (X.presheaf.germ V (genericPoint X) hη).hom ((secMap s V).hom r) =
    (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r))
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 2
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ V le_top) ≫ _ = _
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem germSec_restrictGlobal_algebraMap {V : X.Opens} (hη : genericPoint X ∈ V) (r : k) :
    letI := algΓ s; letI := ffAlg s
    germSec s hη (restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) = algebraMap k X.functionField r := by
  letI := algΓ s; letI := ffAlg s
  change (X.presheaf.germ V (genericPoint X) hη).hom ((X.presheaf.map (homOfLE le_top).op).hom _) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
  rfl

def formGerm (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    letI := algΓ s; letI := ffAlg s
    sectionsOn (Omega s j) V →ₗ[k] DR k X.functionField :=
  letI := algΓ s; letI := ffAlg s
  { toFun := fun x ↦ (semiHom_germSec s hη).mDR
      ((toOmEquiv s j hV).symm (sectionsOn.toΓ _ _ x) : DR k (Sec s V))
    map_add' := fun x y ↦ by
      rw [map_add (f := _), map_add (f := _), Submodule.coe_add, map_add (f := _)]
    map_smul' := fun r x ↦ by
      rw [sectionsOn.toΓ_smul]
      have h1 : (toOmEquiv s j hV).symm (restrictGlobal X V (algebraMap k Γ(X, ⊤) r) •
          sectionsOn.toΓ _ _ x) = (show Sec s V from restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) •
          (toOmEquiv s j hV).symm (sectionsOn.toΓ _ _ x) :=
        (toOmEquiv s j hV).symm.map_smul _ _
      rw [h1, Submodule.coe_smul, SemiHom.mDR_smul]
      change germSec s hη (restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) • _ = _
      rw [germSec_restrictGlobal_algebraMap, algebraMap_smul]
      rfl }

def formGermI (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V)
    [inst : Algebra k X.functionField] (hinst : inst = ffAlg s) :
    letI := algΓ s; sectionsOn (Omega s j) V →ₗ[k] DR k X.functionField := by
  subst hinst; exact formGerm s j hV hη

theorem formGermI_ffAlg (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    formGermI (inst := ffAlg s) s j hV hη rfl = formGerm s j hV hη := rfl

end GlobalTheory.HodgeCoh
