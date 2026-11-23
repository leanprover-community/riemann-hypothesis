module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulSymPairMemSpanBalancedTensors
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep


theorem _root_.GlobalTheory.T.transpose_mul_symPair_mem_span_balancedTensors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (R : Type) [CommRing R] (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (B : Matrix (Fin n) (Fin n') R), (∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0) → ∀ P : GlobalTheory.LogKSDiv.PairIx H Dw, ∃ cf : Fin Dw.dim → R, _root_.Matrix.transpose B * GlobalTheory.LogKSDiv.symPair (R := R) e P * B = ∑ k, cf k • GlobalTheory.LogKSDiv.symPair (R := R) e' (ε' k) := by
  first | exact @GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | exact GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | (intros; apply GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span <;> assumption)
