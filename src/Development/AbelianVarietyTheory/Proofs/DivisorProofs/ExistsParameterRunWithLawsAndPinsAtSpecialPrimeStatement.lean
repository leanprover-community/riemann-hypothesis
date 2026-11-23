module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterRunWithLawsAndPinsAtSpecialPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

theorem _root_.GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), Links2 p → CoreTies L ex.errX p.T (R2 p) → ∀ l : ℕ, (l = D.host.pde ∨ l = D.host.pde') → ∃ r : GlobalTheory.RealIndexBound.RunData p.T, LawsFull r.full ∧ (∀ i : Fin D.R.m, GlobalTheory.FormTies.OneCover r.full.toTop ((i : ℕ) + 1)) ∧ (∀ j n : ℕ, InR D j → (r.full.dδ j n).pd = l) ∧ (∀ i : Fin D.R.m, ∀ γ₀ ∈ Formalism.L2.Theta.GQ (r.full.V ((i : ℕ) + 1) r.full.σ₀), r.full.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (r.full.V ((i : ℕ) + 1) r.full.σ₀) γ₀)) = 1) ∧ ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ i : Fin D.R.m, letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg; RunPin (T := r.full) (R2 p) i (p.κ i).n v (ownAt D v) := by
  first | exact @GlobalTheory.RunOnto.exists_run_pins | exact GlobalTheory.RunOnto.exists_run_pins | (intros; apply GlobalTheory.RunOnto.exists_run_pins <;> assumption)
