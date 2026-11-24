module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

section At

variable (D : D7) (i : D.nd.Loc)

def chiRatio (c : ℕ) : GE D.nd →* (D.nd.O i)ˣ := chiU D.nd i c * (chiU D.nd i 1)⁻¹

def IsConstituent {n : ℕ} (χ : GE D.nd →* (D.nd.O i)ˣ)
    (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i)) : Prop :=
  ∃ v : Fin n → KK D.nd i, v ≠ 0 ∧
    ∀ g, (mapM (toK D.nd i) M g).mulVec v = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • v

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def CharCrysAt (χ : GE D.nd →* (D.nd.O i)ˣ) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (charRep (Br.locChi D.nbr i w hw χ))

def MatCrysAt {n : ℕ} (M : GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw M))

def ChiRatioCrysAt : Prop :=
  ∀ c : ℕ, 1 ≤ c → c ≤ D.R.t →
    chiRatio D i c = (epsU D.nd i) ^ (-((c : ℤ) - 1)) ∧ CharCrysAt D i w hw (chiRatio D i c)

end At

theorem chiRatio_eq (D : D7) (i : D.nd.Loc) (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) :
    chiRatio D i c = (epsU D.nd i) ^ (-((c : ℤ) - 1)) := by
  unfold chiRatio chiU
  rw [D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]
  rfl

theorem chiRatO_apply (D : D7) (i : D.nd.Loc) (c : ℕ) (g : GE D.nd) :
    chiRatO D.nd i c g 0 0 = ((chiRatio D i c g : (D.nd.O i)ˣ) : D.nd.O i) := by
  simp [chiRatO, twistM, chiRatio]

end GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps
