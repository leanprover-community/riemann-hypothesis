module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DescOfDes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.DescTest

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem step_desc (hOut : D.Out l) (hk : k = false ∨ ρ = 0) (r : ℕ) :
    Desc (ε.qk 1 - 1) (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).fn (jE (F.pt κ)) :=
  desc_fil F κ ε k n ρ hρ hk r _ (des_qk hOut ε (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).1 n (ρ r))

theorem xi_thick (T : (F.pt κ).Elements) :
    ((gE F κ k n).obj T).i ((base l).cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i)) ∈ ((gE F κ k n).obj T).J :=
  xi_mem F κ k n T _ ((GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.1 T.1 n)

theorem mu_factor : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i :=
  (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.2.1

end



theorem main : ∀ {l : ℕ} [Fact l.Prime], D.Out l → ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), (k = false ∨ ρ = 0) →
    Desc (Polynomial.X : Polynomial ℤ) (gE F κ k n ⋙ (flt F κ ε k n ρ hρ).rees) (jE (F.pt κ)) := by
  intro l _ hOut O _ F κ ε k n ρ hρ hk
  exact desc_flt (b := bs l k n) (L := Lc F κ k n) (Λ := Acris l) (F.pt κ) ((base l).cris n) (gE F κ k n) ρ hρ
    ε.μ (ε.μ_mem k (base l) n) (jE (F.pt κ)) (ε.qk 1 - 1) (∑ i ∈ Finset.range l, ε.qk 1 ^ i)
    (mu_factor ε) (xi_thick F κ ε k n) (step_desc F κ ε k n ρ hρ hOut hk)

end GlobalTheory.CompanionTheory.DescTest
