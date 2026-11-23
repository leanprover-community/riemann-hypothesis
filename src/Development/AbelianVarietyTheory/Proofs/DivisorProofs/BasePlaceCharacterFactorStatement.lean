module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactor
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)


theorem _root_.GlobalTheory.T.base_place_character_factor : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ),
    ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 →
    ∃ (b : D.what₂.LL) (g g' : 𝓞 D.what₂.LL), GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      g ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      g' ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      ((chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v)) z) =
        D.what₂.embLL (b * ((g : D.what₂.LL) / (g' : D.what₂.LL))) * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) := by
  first | exact @GlobalTheory.SqStepArith.base_place_factor_zero | exact GlobalTheory.SqStepArith.base_place_factor_zero | (intros; apply GlobalTheory.SqStepArith.base_place_factor_zero <;> assumption)
