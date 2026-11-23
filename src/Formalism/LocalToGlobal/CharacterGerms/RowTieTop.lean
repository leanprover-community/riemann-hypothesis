module

public import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import Formalism.LocalToGlobal.CharacterGerms.PlugUP
import ReciprocityTheory.DualLattices.FrobEqOfLe

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem card_sigma_fst {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a).card = m a := by
  rw [show (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a) =
      (Finset.univ : Finset (Fin (m a))).map ⟨Sigma.mk a, sigma_mk_injective⟩ from ?_]
  · simp
  · ext x
    obtain ⟨b, i⟩ := x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      exact (congrArg Sigma.fst hj).symm


open ReciprocityTheory.PGsh.Up CharacteristicFromRanks ValuationFitting

variable {C : Type} [Field C]


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

section Rank

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem rankHyp_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.raw (pairOfLab ha hg o)).RankHyp := by
  refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
  · intro g a hb
    simp only [FBChart.raw, pairOfLab]
    convert
      (card_sigma_fst (fun b => Dw.mult (lab.tau o g b)) a).trans ((hr o).2.1 g a hb)
      using 2
    exact Finset.filter_congr (fun _ _ => Iff.rfl)
  · intro g a hb
    simp only [FBChart.raw, pairOfLab]
    convert
      (card_sigma_fst (fun b => Dw.mult (lab.tau o g b)) a).trans ((hr o).2.2 g a hb)
      using 2
    exact Finset.filter_congr (fun _ _ => Iff.rfl)

end Rank


variable (Xo c)



variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]


end Formalism.L2.FormalSeriesBounds
