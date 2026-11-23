module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart

@[expose] public section

noncomputable section

namespace GlobalTheory.KerJ.CharModel

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

section General

variable {L : Type} [Field L] [NumberField L]

theorem prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  apply _root_.GlobalTheory.Mem.Chr.Determ.exists_prod_inf_mul_finPart <;> assumption

theorem isFin_finPart (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

theorem isUnitary_of_orderDvd {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) : χ.IsUnitary := fun x => by
  have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
  have h2 : χ.1 x ^ n = 1 := by simpa using h1
  have h3 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3

end General

variable {D : D7} {C : CharFrame D} (Dt : DtTied D C) {nch : NChoice D} (Tp : TupTied D C nch)

theorem eDt_finPart (a : Ideles D.host.E) : Dt.eDt (finPartI D.host.E a) = Dt.eDt a := by
  obtain ⟨y, hy⟩ := prod_inf_mul_finPart a
  conv_rhs => rw [← hy]
  rw [map_mul, map_prod, Finset.prod_eq_one fun w _ => Dt.inf w (y w), one_mul]


end GlobalTheory.KerJ.CharModel
