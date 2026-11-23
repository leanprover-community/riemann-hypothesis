module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHkDatAtStateStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IotaRInjectiveStatesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemGoodLIffOfStateStatement
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



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.EigSpanDesc
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Core
theorem spanC_of_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
    Rows.IsotInternal (Dof x).what₂ → GlobalTheory.EigRows.OccGood (Dof x) →
    ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ)
      (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) →
      LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) →
      HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' →
      ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig →
        SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  intro hL
  refine (((_root_.GlobalTheory.T.mem_goodL_iff_iotaR_mem_goodW hL).and (_root_.GlobalTheory.T.iotaR_injective_at_level_a hL)).and (_root_.GlobalTheory.T.exists_hkDat_at_split_place hL)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
  obtain ⟨⟨htie, hinj⟩, hhk⟩ := h
  intro P x hLA hI hG θ hL' hθ hlv _ _ hRd eig hEig
  exact spanC_core x.m.z.R x.m.z.F x.r.Y x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) θ hL' eig hI hG
    (htie P x hLA θ hθ hlv) (hinj P x hLA) (hhk P x hLA) hRd hEig
end GlobalTheory.EigSpanDesc
end
end
