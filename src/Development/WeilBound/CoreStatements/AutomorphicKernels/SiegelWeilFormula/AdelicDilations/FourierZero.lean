module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

structure Hyps : Prop where
  holLead : HolLead
  holT : HolT
  tAll : TAll
  thetaCoef : ThetaCoef
  auxEx : AuxiliaryPrimeFunction
  coefEx : CoefEx
  fockMem : FockMem
  liftEx : LiftEx
  locOpEx : LocOpEx
  locInst : LocInst
  gSplit : GSplit
  polyKFin : PolyKFin
  secK : SecK
  eisWk : EisWk
  lamBd : LamBd
  lamSing : LamSing
  fourierZero : FourierZero
  unfold : Unfold
  whitLow : WhitLow
  vacK : VacK
  iwaQ : IwaQ
  cTSplit : CTSplit
  uEx : UEx
  fcConj : FcConj
  orbRes : OrbRes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def EData (d : SD σ) (f : d.G → ℂ) (s₁ s₀ : ℂ) (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (t : ℝ) : Prop :=
  IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ p ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (Ê · g) U) ∧ ContinuousOn (fun y : ℂ × d.G => Ê y.1 y.2) (U ×ˢ Set.univ) ∧
    (∀ z ∈ U, ∀ γ ∈ rat2 σ d.Y, ∀ g, Ê z (γ * g) = Ê z g) ∧
    ∀ z : ℂ, t < z.re → (∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q) ∧
      ∀ g, Ê z g = p.eval z * d.eis f s₁ z g

def avg (d : SD σ) (L : LD d) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n → AE F E))
    (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b)) (𝓖 : Set (nA σ d.Y d.b)) (φ : d.G → ℂ) (T : nF σ d.Y d.b)
    (x : d.G) : ℂ :=
  ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) ∂ν

def cOne (d : SD σ) (L : LD d) (f : d.G → ℂ) (s₁ z : ℂ) (nb' : nA σ L.Y L.b → L.sd.G) (lam' : Measure (nA σ L.Y L.b))
    (𝓖' : Set (nA σ L.Y L.b)) (T' : nF σ L.Y L.b) (x : d.G) : ℂ :=
  fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
    ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1

end PositivityTheory.SiegelWeilFormula.AStep

end
