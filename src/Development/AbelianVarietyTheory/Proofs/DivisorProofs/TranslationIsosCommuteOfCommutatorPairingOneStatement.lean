module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsosCommuteOfCommutatorPairingOne
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT


theorem _root_.GlobalTheory.T.translation_isos_commute_of_commutatorPairing_one : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (L : LB G.left), L.IsLB → ∀ (x y : 𝟙_ (Over S) ⟶ G) (φx : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl x).left] ![1, -1])) (φy : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl y).left] ![1, -1])), φx.IsGen → φy.IsGen → Out.WeilIs G L 1 x y 1 → LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ φx (LB.pullGen L _ _ φy (GlobalTheory.UPel.HT.Hecke.transl x).left)) (LB.mulGen L _ _ _ _ φy (LB.pullGen L _ _ φx (GlobalTheory.UPel.HT.Hecke.transl y).left)) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs | exact GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs | (intros; apply GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs <;> assumption)
