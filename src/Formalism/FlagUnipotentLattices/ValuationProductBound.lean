import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SuperdiagonalAdditionInvariance

namespace Formalism.HermitianLatticeCounting.Final.S4

theorem tauLin : Formalism.HermitianLatticeCounting.S4.TauLin := Formalism.HermitianLatticeCounting.P.involution_map_linear
theorem tauHom : Formalism.HermitianLatticeCounting.S4.TauHom := Formalism.HermitianLatticeCounting.P.involution_map_hom
theorem homCount : Formalism.HermitianLatticeCounting.S4.HomCount := Formalism.HermitianLatticeCounting.P.hom_count_symmetric_group
theorem assemblyNG : Formalism.HermitianLatticeCounting.S4.AssemblyNG := Formalism.HermitianLatticeCounting.P.hermitian_count_assembly
theorem assemblyNG2 : Formalism.HermitianLatticeCounting.S4.AssemblyNG2 := Formalism.HermitianLatticeCounting.P.hermitian_count_assembly_of_type
theorem projW : Formalism.HermitianLatticeCounting.S4.ProjW := Formalism.HermitianLatticeCounting.P.projection_weight_formula
theorem weightedCS : Formalism.HermitianLatticeCounting.S4.WeightedCS := Formalism.HermitianLatticeCounting.P.weighted_cauchy_schwarz
theorem omCount : Formalism.HermitianLatticeCounting.S4.OmCount := Formalism.HermitianLatticeCounting.P.orbit_count_formula
theorem step4 : Formalism.HermitianLatticeCounting.S4.Step4 := Formalism.HermitianLatticeCounting.P.fourth_reduction_identity

end Formalism.HermitianLatticeCounting.Final.S4
