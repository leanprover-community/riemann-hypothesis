module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbFin :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.OrbProper → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.NormEx → UpperTheory.V.Z.Tf.Orb.QuotInt → UpperTheory.V.Z.Tf.Orb.QuotPos → UpperTheory.V.Z.Tf.Orb.TwOrbFin := by
  intro hG hX hC hP hH hN hI hQ k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE φ hφ hc δ hδ μ hμ
  obtain ⟨g1, g2, g3, g4, -⟩ := hG E n
  obtain ⟨c1, c2⟩ := hC k E σ hσ n δ hδ
  obtain ⟨-, i2, i3⟩ := hH _ _ c1 c2 μ hμ
  have hs := ((hX k E).2.2 n).2 σ
  obtain ⟨ρ, hρ, -⟩ := hN _ g4 _ c1 μ hμ i3
  have hF : Continuous fun g => φ (twConj (sigmaGL σ) g δ) := hφ.comp ((continuous_inv.mul continuous_const).mul hs)
  have hinv : ∀ h ∈ twCent (sigmaGL σ) δ, ∀ g, φ (twConj (sigmaGL σ) (h * g) δ) = φ (twConj (sigmaGL σ) g δ) :=
    fun h hh g => by rw [twConj_mul_left _ _ hh]
  have hM : CptMod (twCent (sigmaGL σ) δ) fun g => φ (twConj (sigmaGL σ) g δ) := by
    obtain ⟨D, hD, h⟩ := hP k E σ hσ n δ hδ _ hc
    exact ⟨D, hD, fun g hg => h g (subset_tsupport _ hg)⟩
  exact ⟨⟨ρ, hρ⟩, hI _ μE hμE _ c1 μ hμ i2 _ hF hinv hM,
    fun p q => hQ _ μE hμE _ c1 μ hμ i2 ⟨ρ, hρ⟩ _ hF hinv hM (fun g => p _) q⟩
