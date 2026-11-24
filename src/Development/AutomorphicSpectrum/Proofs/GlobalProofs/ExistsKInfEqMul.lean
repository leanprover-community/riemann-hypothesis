module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf

open GlobalTheory.Published.AutFin

variable {D : D7}

def kInf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) : GA D V :=
  (Finset.univ.toList.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {ε : D.what₂.Tau → Fin V.rank → Bool}
  {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem kAt_comm (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) (k : Formalism.REAL.KG (ε τ))
    (k' : Formalism.REAL.KG (ε τ')) :
    Commute (kAt θ V τ (ε τ) (fr τ) k) (kAt θ V τ' (ε τ') (fr τ') k') :=
  GlobalTheory.AvgOtherPlace.atTau_comm hθ hne (conj_mem_UH (hfr τ).1 (hfr τ).2 k) (conj_mem_UH (hfr τ').1 (hfr τ').2 k')

theorem exists_kInf_eq_mul (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) (a : D.what₂.Tau) :
    ∃ y : GA D V, ∀ κ' : ∀ τ, Formalism.REAL.KG (ε τ), (∀ τ, τ ≠ a → κ' τ = κ τ) →
      kInf θ V ε fr κ' = y * kAt θ V a (ε a) (fr a) (κ' a) := by
  classical
  let f : (∀ τ, Formalism.REAL.KG (ε τ)) → D.what₂.Tau → GA D V := fun κ τ => kAt θ V τ (ε τ) (fr τ) (κ τ)
  have hperm : (Finset.univ : Finset D.what₂.Tau).toList.Perm (a :: (Finset.univ.erase a).toList) := by
    have := Finset.toList_insert (Finset.notMem_erase a (Finset.univ : Finset D.what₂.Tau))
    rwa [Finset.insert_erase (Finset.mem_univ a)] at this
  refine ⟨((Finset.univ.erase a).toList.map (f κ)).prod, fun κ' hκ' => ?_⟩
  have hpw : ((Finset.univ : Finset D.what₂.Tau).toList.map (f κ')).Pairwise Commute :=
    List.pairwise_map.2 ((Finset.nodup_toList _).imp fun {τ τ'} hne => kAt_comm hθ hfr (Ne.symm hne) _ _)
  have e1 : kInf θ V ε fr κ' = f κ' a * ((Finset.univ.erase a).toList.map (f κ')).prod := by
    rw [kInf, (hperm.map (f κ')).prod_eq' hpw, List.map_cons, List.prod_cons]
  have e2 : (Finset.univ.erase a).toList.map (f κ') = (Finset.univ.erase a).toList.map (f κ) :=
    List.map_congr_left fun τ hτ => by
      simp only [f, hκ' τ (Finset.ne_of_mem_erase (Finset.mem_toList.1 hτ))]
  rw [e1, e2]
  refine (Commute.list_prod_right _ _ fun x hx => ?_).eq
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hx
  exact kAt_comm hθ hfr (Finset.ne_of_mem_erase (Finset.mem_toList.1 hτ)) _ _

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf
