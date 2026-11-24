module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)

def Congr (a b : G ℚ Ω →* c.Oˣ) : Prop := ∀ σ, ((a σ : c.Oˣ) : c.O) - ((b σ : c.Oˣ) : c.O) ∈ IsLocalRing.maximalIdeal c.O

def IsOmT (w : G ℚ Ω →* c.Oˣ) : Prop :=
  w ^ (l - 1) = 1 ∧ Congr c w (UpperTheory.V.Base.chiO (k := ℚ) (Ω := Ω) l c.O)

structure GDlit (K : Type) [Field K] [NumberField K] [Algebra K Ω] (e : ℕ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (w η : G ℚ Ω →* c.Oˣ) (a : ℕ) : Prop where
  om : IsOmT c w
  eta_ker : η.ker = galOf ℚ K Ω
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  N_even : Even N
  ord : ¬ l ∣ orderOf (Chr.dirG ℚ Ω ψ)
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ σ = w σ ^ a
  a_lt : a < l - 1
  two_a : l - 1 ∣ 2 * a
  par : ∀ σ : G ℚ Ω, IsCC σ → UpperTheory.V.Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1
  quad : Module.finrank ℚ K = 2
  imag : IsTotallyComplex K
  l_cop : ¬ l ∣ (discr K).natAbs * classNumber K
  cop : (discr K).natAbs.Coprime N
  eta : ∀ i j : ℕ, ¬ Congr c η (w ^ i * (Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹) ^ j)
  gen : ¬ l - 1 ∣ 2 * (e + a)

end UpperTheory.V.HV

end
