module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.TrueGeo GlobalTheory.TrueCx
open scoped ContDiff

def cutoff (y : ℝ) : ℝ := Real.smoothTransition (3 - y) ^ 2

def cutWt (κ R r : ℝ) : ℝ := cutoff (Real.log r / Real.log R) / (1 + (r / R) ^ κ)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ)

def OddPrimesWithRootsOfUnity.eigMet : EigMet Z σ := .ofForm (x.met σ) (x.met_smooth σ).1

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

namespace ToroidalCompactificationData

variable (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ)

def hodge : EigMet s.T.Z σ :=
  .hodge s.U (2 * Real.pi * xiR D) (mul_pos Real.two_pi_pos (xiR_pos D)) (x.eigMet σ)

variable {σ} {y : CxPts (genStr s.T.Z) σ}

def IsMuExp (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ), ¬ LiesIn y (genBd s.T.Z) →
    ∀ (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ),
      x.r σ y ^ (-C) * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re ≤ (star v ⬝ᵥ ((_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ).gram y g τ *ᵥ v).re ∧
        (star v ⬝ᵥ ((_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ).gram y g τ *ᵥ v).re ≤ x.r σ y ^ C * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re

def muExp : ℝ := Classical.epsilon x.IsMuExp

def kap : ℝ := 2 * x.muExp + 3

open Classical in
variable (σ) in
def wt (R : ℝ) (y : CxPts (genStr s.T.Z) σ) : ℝ :=
  if LiesIn y (genBd s.T.Z) then 0 else cutWt x.kap (max R 2) (x.r σ y)

variable (σ) in
def eigMetAt : Option ℝ → EigMet s.T.Z σ
  | none => (_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ
  | some R => .interp (x.wt σ R) (x.wt_mem R) (x.eigMet σ) ((_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ)

end ToroidalCompactificationData

variable (x : ToroidalCompactificationData s) (Φ : s.Flag)

def metsOf : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL) := fun k R σ n => (Φ.C k).met (x.eigMetAt (embOf κ.e σ) R) n

def refMet : ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n) :=
  fun k σ n => (Φ.C k).met (x.eigMet (embOf κ.e σ)) n

def rFlag : ∀ k σ, Pts (Φ.C k).Y σ → ℝ := fun k σ p => x.r (embOf κ.e σ) ((Φ.C k).down p)

variable (k : s.Comp) (R : Option ℝ) (σ : D.what₂.LL →+* ℂ) (n n' : Letter S.Dw → ℤ)

variable {x Φ k σ n} {p : Pts (Φ.C k).Y σ}

end GlobalTheory.ShFam
