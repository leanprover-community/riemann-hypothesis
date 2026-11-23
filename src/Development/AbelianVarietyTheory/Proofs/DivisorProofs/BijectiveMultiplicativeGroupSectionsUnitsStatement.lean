module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.Algebra.Category.Grp.Adjunctions
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.bijective_multiplicativeGroup_sections_units :
    ∀ U : Scheme.{0}, Function.Bijective (ofRings.sec unitsF U) := by
  have hGamma : Presheaf.IsSheaf Scheme.etaleTopology.{0} Scheme.Γ := by
    intro R
    have gammaIso : Scheme.Γ ⋙ coyoneda.obj (op R) ≅ yoneda.obj (Spec R) :=
      NatIso.ofComponents
        (fun U => (Equiv.trans (Quiver.Hom.opEquiv)
          (ΓSpec.adjunction.homEquiv U.unop (op R))).toIso)
        (by
          intro U V f
          ext g
          exact ΓSpec.adjunction.homEquiv_naturality_left f.unop g.op)
    exact Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (Presieve.isSheaf_iso _ gammaIso.symm
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
  have hUnits : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ unitsF) := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
    let F := forget₂ CommRingCat.{0} CommMonCat ⋙ CommMonCat.units ⋙
      forget CommGrpCat ⋙ uliftFunctor.{1, 0}
    have hF : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ F) :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ F hGamma
    exact hF
  intro U
  have := isIso_toSheafify Scheme.etaleTopology hUnits
  delta ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U))
