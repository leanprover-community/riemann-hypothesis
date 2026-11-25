module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIff
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.HSNef

theorem isNef_pull : GlobalTheory.Published.ArCalc → SemiPull → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E →
    ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.IsNef D → (L.pull π hπ).IsNef E := by
  intro hA hS k _ X Y _ _ p q D E hX hY π hπ L hN
  obtain ⟨h, hh⟩ := ((hA.arExists k X p D hX).1 L)
  obtain ⟨h', hh'⟩ := ((hA.arExists k Y q E hY).1 (L.pull π hπ))
  have hL := (hh.isNef_iff hX).1 hN
  refine (hh'.isNef_iff hY).2 ⟨hS k X Y p q D E hX hY π hπ L hN.semiPos, fun Z i _ _ hd => ?_⟩
  rw [GlobalTheory.MixHt.heightProj k X Y p q D E hX hY π hπ L h h' hh hh' (i (genericPoint Z))]
  by_cases h0 : π.residueDegree (i (genericPoint Z)) = 0
  · simp [h0]
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  have hAY := GlobalTheory.MixHt.isAmb_of_isArithVar hY
  have hAX := GlobalTheory.MixHt.isAmb_of_isArithVar hX
  obtain ⟨-, -, -, -, hcl, hgd⟩ := GlobalTheory.MixHt.hasDim_basic k Y q hAY
  obtain ⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩ := GlobalTheory.MixHt.hasDim_basic k X p hAX
  have hy : GlobalTheory.MixHt.HasDim (i (genericPoint Z)) 1 := (hcl Z i _ 1).2 ((hgd Z 1).2 (by exact_mod_cast hd))
  obtain ⟨d', -, hd'⟩ := hm' (π (i (genericPoint Z)))
  obtain ⟨-, hiff⟩ := GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ _ 1 d' hy hd'
  have e1 : 1 = d' := hiff.1 h0
  subst e1
  obtain ⟨W, j, _, _, hj⟩ := exists_isClosedImmersion_genericPoint (π (i (genericPoint Z)))
  have hW : topologicalKrullDim W = (1 : ℕ) := (hgd' W 1).1 ((hcl' W j _ 1).1 (hj ▸ hd'))
  have := hL.2 W j (by exact_mod_cast hW)
  rwa [hj] at this

end GlobalTheory.HSNef
