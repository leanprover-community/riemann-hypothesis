module

public import Development.EtaleCohomology.WeilConjectures.GluePf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EWeil.Gys.LV.GluePf

theorem shvSigma : ShvSigma := by
  intro R _ F T Y c hc
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le G Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ G).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget _)).1 F.property))
  have : PreservesLimitsOfShape (Discrete T) G := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let hL : IsLimit (G.mapCone c.op) := isLimitOfPreserves G (Cofan.IsColimit.op hc)
  let e := Types.isLimitEquivSections hL
  have he : ∀ s t, (e s).1 ⟨t⟩ = GlobalTheory.EtC.Sec.res (c.inj t) s := fun s t => rfl
  constructor
  · intro s₁ s₂ h
    apply e.injective
    apply Subtype.ext
    funext ⟨t⟩
    rw [he, he]
    exact congrFun h t
  · intro y
    let sec : (Discrete.functor (fun a => op (Y a)) ⋙ G).sections :=
      ⟨fun j => y j.as, by
        rintro ⟨j⟩ ⟨j'⟩ ⟨h⟩
        cases h
        show G.map (𝟙 _) _ = _
        rw [G.map_id]; rfl⟩
    refine ⟨e.symm sec, ?_⟩
    funext t
    show GlobalTheory.EtC.Sec.res (c.inj t) (e.symm sec) = y t
    rw [← he, e.apply_symm_apply]

end LateralTheory.EWeil.Gys.LV.GluePf
