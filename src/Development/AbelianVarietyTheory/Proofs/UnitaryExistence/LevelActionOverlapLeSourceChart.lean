module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.LevActCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem levelAction_overlap_le_source_chart {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) (x : Sp S ⟶ Xo.X)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      (PPx x).U (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hz.2

theorem overlap_le_tgt {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) {x x' : Sp S ⟶ Xo.X}
    (pm : Gx x ⟶ Gx x')
    (hp : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ φ)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      pm ⁻¹ᵁ (PPx x').U (fun _ => i) := by
  intro z hz
  have h1 : ((snd (Over.mk x) Xo.univ.t.G).left ≫ φ).base z ∈ (Xo.univ.t.PP.L.U i : Set _) :=
    Set.mem_iInter.1 hz.1 PUnit.unit
  rw [← hp] at h1
  exact Set.mem_iInter.2 fun _ => h1

end GlobalTheory.LevActCompare
