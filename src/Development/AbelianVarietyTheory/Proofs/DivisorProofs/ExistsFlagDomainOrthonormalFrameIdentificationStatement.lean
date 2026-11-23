module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
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

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification : ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) → ∀ A : Frames V, IsFrames V A → ∃ (X₀ : Data D.host.E V.rank) (σ : D.what₂.Tau ≃ X₀.Ψ) (x : Frame X₀.Ψ V.rank) (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank), X₀.Gm = -(V.gram)ᵀ ∧ (∀ ρ, (σ ρ).1 = tauE D ρ) ∧ IsOrth X₀ x ∧ IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) X₀.Ψ X₀.Gm x σ A e := by
  first | exact @GlobalTheory.CovTop.VolUp.exists_ident_frame | exact GlobalTheory.CovTop.VolUp.exists_ident_frame | (intros; apply GlobalTheory.CovTop.VolUp.exists_ident_frame <;> assumption)
