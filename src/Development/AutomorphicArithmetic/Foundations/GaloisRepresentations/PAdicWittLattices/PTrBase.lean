module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
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
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTrBase :
    FEtBasic → SplitsBasic → GalClosD → TrBase.{u} := by
  intro hF hS hC B R _ T hT P Y Z' Z p q p' q' v s' s g d hv hg hq' hpb hs tr tr' htr htr' x
  haveI : IsFinite s := hs.1
  haveI : Etale s := hs.2.1
  obtain ⟨W, c, G, _, _, a, σ, hgal, hspl⟩ := hC s' d (hF.1 v s' s g d hpb hs)
  have hσs : ∀ j, σ j ≫ s' = c := hspl.1
  have hσ' : ∀ j, σ j ≫ q' = c ≫ p' := fun j => by
    rw [← hq', ← Category.assoc, hσs j]
  have hσv : ∀ j, (σ j ≫ v) ≫ q = c ≫ p' := fun j => by
    rw [Category.assoc, hv, hσ' j]
  have hcg : (c ≫ g) ≫ p = c ≫ p' := by rw [Category.assoc, hg]
  have hspl2 : Splits s (c ≫ g) (fun j => σ j ≫ v) :=
    (hS.2 v s' s g hpb c (Fin d) σ hσs).1 hspl
  apply hT.inj p' (c ≫ p') c rfl G a hgal
  rw [← T.pull_comp c g rfl hg hcg, htr W (c ≫ p') (c ≫ g) hcg (Fin d) (fun j => σ j ≫ v) hσv hspl2 x,
    htr' W (c ≫ p') c rfl (Fin d) σ hσ' hspl]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact T.pull_comp (σ j) v (hσ' j) hv (hσv j) x
