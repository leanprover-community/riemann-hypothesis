import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfinitelyManySplitPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.PlacesTest

variable {D : D7}

theorem exists_one_place (D : D7) (Z : Finset (Pl D)) : ∃ (v : Pl D) (p : SplitPt D (Fv D.host.F v)),
    v ∉ Z ∧ Places (fun _ : Unit => p) [()] (· = v) := by
  have h := ((GlobalTheory.FinPl.AlmostAll.latA_eq_latV D).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    (GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹))).and Z.eventually_cofinite_notMem
  obtain ⟨v, ⟨e, ε, he, hε, hs⟩, ⟨h1, h2, h3⟩, hZ⟩ :=
    ((Set.infinite_iff_frequently_cofinite.1 (infinite_splitIdem_places D)).and_eventually h).exists
  obtain ⟨p, -, hp⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he hε hs
  refine ⟨v, p, hZ, by simp, by simp, fun _ _ _ => rfl, fun x => by simp [hp], fun _ => ?_⟩
  unfold SplitPt.UnitAA
  rw [hp]
  exact ⟨fun a ha => ⟨h2 a ha, h3 a ha⟩, h1⟩

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}




variable {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S} {LT : Lat T}


theorem vac_zero (P : Pl D → Prop) : Vac ψ S T LS LT P 0 := by
  have h : ∀ u, heisO ψ S T u 0 = 0 := fun u => by funext w; simp [heisO]
  exact ⟨⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => h u⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩,
    fun u _ => h _, fun _ _ u _ _ => h u⟩


end

theorem symplOH_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (x y : WO S L'') :
    symplOH L S (kap τ S x) (kap τ S y) = symplOH S L'' x y := by
  have := GlobalTheory.LinkKappa.symplO_ofAdj L L'' S τ (-1) (by simpa using hτ) x y
  simp only [symplOH, kap, this]
  simp

theorem kap_add {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (x y : WO S L'') :
    kap τ S (x + y) = kap τ S x + kap τ S y := by
  simp only [kap, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, Matrix.mul_add, adj_add, Matrix.add_mul, smul_add]




end GlobalTheory.FinPl.PlacesTest

end
