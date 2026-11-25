module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmooth

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

theorem _root_.GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m → I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) ∧ I.A.ESmooth (B.R.N i) (B.R.N (i + 1)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true
