module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.joinAbs_of :
    NilEmb → NilSubq → NilOfAnn → AnnSub → AnnExt → AdmExact → JoinAbs := by
  intro hEmb hSubq hOfAnn hAnnSub hAnnExt hAdmExact
  intro F G B _ _ _ _ σ ψ hσψ L _ _ e hB V _ _ _ ρ q n T hAdm hAnn U _ _ ρU i TU θ hi hinj hT hTg hTT hnil
    W _ _ _ _ ρW I _ C _ _ ρC f hsub hf hsep
  letI : Module F U := Module.compHom _ (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : ∀ a, Module F (C a) := fun a => Module.compHom _ (algebraMap F L)
  haveI : ∀ a, IsScalarTower F L (C a) := fun a => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  obtain ⟨hE1, hE2⟩ := hAnnExt F G B σ ψ L V ρ
  have hAdmL := hE1 e hAdm
  have hAnnL := hE2 q n T hAnn
  have hAdmU : admitted σ e ρU :=
    (hAdmExact F G B σ L e hB U (L ⊗[F] V) ρU (extRep L ρ) i hi).1 hinj hAdmL
  have hAnnU : AnnD σ ψ q n ρU TU :=
    hAnnSub F G B σ ψ L U (L ⊗[F] V) ρU (extRep L ρ) i hi hinj q n TU
      (fun j => (T j).baseChange L) hT hAnnL
  have hNilU : NilD σ ψ ρU (heckePol q n θ) :=
    hOfAnn F G B σ ψ hσψ L U ρU q n TU θ hTg hTT hnil hAnnU
  have hNilC : ∀ a, NilD σ ψ (ρC a) (heckePol q n θ) := fun a =>
    (hSubq F G B σ ψ L e hB U (C a) ρU (ρC a) (hsub a) hAdmU).2 _ hNilU
  exact hEmb F G B σ ψ L W ρW I C ρC f hf hsep _ hNilC
