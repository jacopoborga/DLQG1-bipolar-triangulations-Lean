"""Bounded negative controls for the exact comparator Challenge-hole exception."""
import copy,hashlib,json,sys,unittest
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'scripts'))
from check_release import ROOT,check_challenge_config,check_challenge_text,check_proof_tokens,load_challenges
BASE='module\nnamespace Test\ntheorem result : True := by\n  sorry\nend Test\n'
class ChallengeHoles(unittest.TestCase):
 def test_compared_terminal_hole(self):check_proof_tokens('Challenge.lean',BASE,['Test.result'])
 def test_production_hole_rejected(self):
  with self.assertRaises(ValueError):check_proof_tokens('DirectedDistances/Example.lean',BASE)
 def test_solution_hole_rejected(self):
  with self.assertRaises(ValueError):check_proof_tokens('Palomar/Pilot/Solution.lean',BASE)
 def test_extra_tactic_before_hole_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('  sorry','  skip\n  sorry'),['Test.result'])
 def test_extra_tactic_after_hole_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('  sorry','  sorry\n  trivial'),['Test.result'])
 def test_noncompared_declaration_hole_rejected(self):
  text=BASE.replace('end Test','theorem extra : True := by sorry\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_renamed_declaration_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('result :','different :'),['Test.result'])
 def test_nested_comment_is_masked(self):
  check_challenge_text(BASE.replace('  sorry','  /- sorry /- admit -/ -/ sorry'),['Test.result'])
 def test_admit_is_never_allowed(self):
  with self.assertRaises(ValueError):check_proof_tokens('Challenge.lean',BASE.replace('sorry','admit'),['Test.result'])
 def test_custom_axiom_is_never_allowed(self):
  with self.assertRaises(ValueError):check_proof_tokens('Challenge.lean',BASE+'axiom bad : False\n',['Test.result'])
 def test_hole_in_noncompared_definition_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE+'def extra : True := by sorry\n',['Test.result'])
 def test_actual_exact_challenges_and_configurations(self):
  specs=load_challenges()
  base={'Palomar/Pilot/Challenge.lean','Palomar/AppendixA/Challenge.lean'}
  self.assertEqual(sum(len(specs[p]['declarations']) for p in base),7)
  self.assertTrue(all(s['declarations'] for s in specs.values()))
 def test_config_name_mismatch_rejected(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['theorem_names']=['Test.other']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_config_extra_kernel_key_rejected(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['external_kernels']=[]
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_config_nanoda_required(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['enable_nanoda']=False
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_proved_public_typing_auxiliary_allowed(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_1']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  check_challenge_config(spec,config)
 def test_typing_auxiliary_is_not_an_extra_hole(self):
  with self.assertRaises(ValueError):
   check_challenge_text(BASE+'theorem DirectedDistances.Example.record._proof_1 : True := by sorry\n',['Test.result'])
 def test_arbitrary_auxiliary_name_rejected(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['Test.unreviewed']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_duplicate_proved_auxiliary_rejected(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  name='DirectedDistances.Example.record._proof_1'
  spec['proved_auxiliaries']=[name,name]
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_definition_holes_remain_forbidden_with_typing_auxiliary(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_1']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  config['definition_names']=['DirectedDistances.Example.data']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_typing_auxiliary_budget_enforced(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_'+str(i) for i in range(13)]
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_named_proved_characterization_allowed_only_in_finite_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['path']='Palomar/Principal/BoltzmannDistances/Challenge.lean'
  spec['declarations']=['DLQG1.Palomar.Principal.boltzmann_distances']
  spec['solution_path']='Palomar/Principal/BoltzmannDistances/Solution.lean'
  spec['proved_auxiliaries']=['DirectedDistances.PlanarMap.mem_sourceSinkPathLengthsBase']
  config['challenge_module']='Palomar.Principal.BoltzmannDistances.Challenge'
  config['solution_module']='Palomar.Principal.BoltzmannDistances.Solution'
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  check_challenge_config(spec,config)
 def test_named_proved_characterization_rejected_in_other_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.PlanarMap.mem_sourceSinkPathLengthsBase']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_actual_probability_theorem_allowed_only_for_cells(self):
  for module in ['CellLDP','CellSDP']:
   spec=copy.deepcopy(next(iter(load_challenges().values())))
   config=json.loads((ROOT/spec['config']).read_text())
   spec['path']='Palomar/Principal/'+module+'/Challenge.lean'
   spec['solution_path']='Palomar/Principal/'+module+'/Solution.lean'
   spec['declarations']=['DLQG1.Palomar.Principal.cell_ldp' if module=='CellLDP' else 'DLQG1.Palomar.Principal.cell_sdp']
   spec['proved_auxiliaries']=['DirectedDistances.RandomWalk.instIsProbabilityMeasureFinOfNatNatUniformCodeMeasure']
   config['challenge_module']='Palomar.Principal.'+module+'.Challenge'
   config['solution_module']='Palomar.Principal.'+module+'.Solution'
   config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
   check_challenge_config(spec,config)
 def test_actual_probability_theorem_rejected_for_unrelated_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.RandomWalk.instIsProbabilityMeasureFinOfNatNatUniformCodeMeasure']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def busemann_typing_fixture(self):
  from check_release import BUSEMANN_TYPING_AUXILIARIES
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['path']='Palomar/Principal/Busemann/Challenge.lean'
  spec['solution_path']='Palomar/Principal/Busemann/Solution.lean'
  spec['declarations']=['DLQG1.Palomar.Principal.busemann']
  spec['proved_auxiliaries']=sorted(BUSEMANN_TYPING_AUXILIARIES)
  config['challenge_module']='Palomar.Principal.Busemann.Challenge'
  config['solution_module']='Palomar.Principal.Busemann.Solution'
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  return spec,config
 def test_exact_busemann_thirteen_typing_certificates_allowed(self):
  spec,config=self.busemann_typing_fixture()
  check_challenge_config(spec,config)
 def test_busemann_thirteen_certificates_wrong_path_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['path']='Palomar/Principal/CellLDP/Challenge.lean'
  spec['solution_path']='Palomar/Principal/CellLDP/Solution.lean'
  config['challenge_module']='Palomar.Principal.CellLDP.Challenge'
  config['solution_module']='Palomar.Principal.CellLDP.Solution'
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_busemann_thirteen_changed_certificate_set_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['proved_auxiliaries'][-1]='DirectedDistances.Example.unreviewed._proof_999'
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_busemann_fourteen_typing_certificates_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['proved_auxiliaries'].append('DirectedDistances.Example.unreviewed._proof_999')
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_attributed_compared_theorem_hole_allowed(self):
  check_challenge_text(BASE.replace('theorem result','@[simp] theorem result'),['Test.result'])
 def test_attributed_definition_after_hole_is_new_command(self):
  text=BASE.replace('end Test','@[expose] noncomputable def next : Nat := 0\nend Test')
  check_challenge_text(text,['Test.result'])
 def test_tactic_after_hole_before_attributed_definition_rejected(self):
  text=BASE.replace('  sorry','  sorry\n  trivial').replace('end Test','@[expose] def next : Nat := 0\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_attributed_unlisted_theorem_hole_rejected(self):
  text=BASE.replace('end Test','@[simp] theorem extra : True := by sorry\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_global_instance_attribute_after_hole_allowed(self):
  text=BASE.replace('end Test','attribute [instance] result\nend Test')
  check_challenge_text(text,['Test.result'])
 def test_indented_attribute_cannot_hide_extra_proof_steps(self):
  text=BASE.replace('  sorry','  sorry\n  attribute [simp] result\n  trivial')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_global_attribute_cannot_hide_unlisted_hole(self):
  text=BASE.replace('end Test','attribute [simp] result\ntheorem extra : True := by sorry\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_exact_convergence_thirteen_certificates_allowed(self):
  spec,config=self.busemann_typing_fixture()
  spec['path']='Palomar/Principal/BusemannConvergence/Challenge.lean'
  spec['solution_path']='Palomar/Principal/BusemannConvergence/Solution.lean'
  config['challenge_module']='Palomar.Principal.BusemannConvergence.Challenge'
  config['solution_module']='Palomar.Principal.BusemannConvergence.Solution'
  check_challenge_config(spec,config)
 def test_convergence_fourteenth_certificate_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['path']='Palomar/Principal/BusemannConvergence/Challenge.lean'
  spec['solution_path']='Palomar/Principal/BusemannConvergence/Solution.lean'
  config['challenge_module']='Palomar.Principal.BusemannConvergence.Challenge'
  config['solution_module']='Palomar.Principal.BusemannConvergence.Solution'
  spec['proved_auxiliaries'].append('DirectedDistances.Example.record._proof_999')
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_shared_identified_support_may_import_validated_busemann_solution(self):
  from check_release import allowed_palomar_import
  self.assertTrue(allowed_palomar_import('Palomar/Principal/Support/BusemannIdentified.lean','Palomar.Principal.Busemann.Solution'))
 def test_other_support_cannot_import_arbitrary_solution(self):
  from check_release import allowed_palomar_import
  self.assertFalse(allowed_palomar_import('Palomar/Principal/Support/Other.lean','Palomar.Principal.Busemann.Solution'))
 def test_production_cannot_import_palomar_solution_or_support(self):
  from check_release import allowed_palomar_import
  self.assertFalse(allowed_palomar_import('DirectedDistances/Example.lean','Palomar.Principal.Busemann.Solution'))
  self.assertFalse(allowed_palomar_import('DirectedDistances/Example.lean','Palomar.Principal.Support.BusemannIdentified'))
 def test_challenge_cannot_import_support(self):
  from check_release import allowed_palomar_import
  self.assertFalse(allowed_palomar_import('Palomar/Principal/BusemannConvergence/Challenge.lean','Palomar.Principal.Support.BusemannIdentified'))
 def convergence_order_fixture(self):
  spec,config=self.busemann_typing_fixture()
  spec['path']='Palomar/Principal/BusemannConvergence/Challenge.lean'
  spec['solution_path']='Palomar/Principal/BusemannConvergence/Solution.lean'
  config['challenge_module']='Palomar.Principal.BusemannConvergence.Challenge'
  config['solution_module']='Palomar.Principal.BusemannConvergence.Solution'
  spec['declarations'].append('DLQG1.Palomar.Principal.busemann_convergence')
  order=[spec['declarations'][0]]+spec['proved_auxiliaries']+[spec['declarations'][1]]
  spec['comparison_order']=order
  config['theorem_names']=list(order)
  return spec,config
 def test_exact_interleaved_convergence_target_order_allowed(self):
  spec,config=self.convergence_order_fixture()
  check_challenge_config(spec,config)
 def test_interleaved_order_cannot_add_or_omit_targets(self):
  spec,config=self.convergence_order_fixture()
  spec['comparison_order'][-1]='DLQG1.Palomar.Principal.unreviewed'
  config['theorem_names']=list(spec['comparison_order'])
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_interleaved_order_cannot_duplicate_targets(self):
  spec,config=self.convergence_order_fixture()
  spec['comparison_order'][-1]=spec['comparison_order'][0]
  config['theorem_names']=list(spec['comparison_order'])
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_interleaved_order_must_match_exact_configuration(self):
  spec,config=self.convergence_order_fixture()
  config['theorem_names']=list(reversed(config['theorem_names']))
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_order_exception_cannot_spread_to_other_configuration(self):
  spec,config=self.busemann_typing_fixture()
  spec['comparison_order']=list(config['theorem_names'])
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_exact_property_tail_thirteen_certificates_allowed(self):
  for module in ['BusemannIncrements','BusemannTails']:
   spec,config=self.busemann_typing_fixture()
   spec['path']='Palomar/Principal/'+module+'/Challenge.lean'
   spec['solution_path']='Palomar/Principal/'+module+'/Solution.lean'
   config['challenge_module']='Palomar.Principal.'+module+'.Challenge'
   config['solution_module']='Palomar.Principal.'+module+'.Solution'
   check_challenge_config(spec,config)
 def test_property_thirteen_changed_set_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['path']='Palomar/Principal/BusemannIncrements/Challenge.lean'
  spec['solution_path']='Palomar/Principal/BusemannIncrements/Solution.lean'
  config['challenge_module']='Palomar.Principal.BusemannIncrements.Challenge'
  config['solution_module']='Palomar.Principal.BusemannIncrements.Solution'
  spec['proved_auxiliaries'][-1]='DirectedDistances.Example.record._proof_999'
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_tail_fourteen_certificates_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['path']='Palomar/Principal/BusemannTails/Challenge.lean'
  spec['solution_path']='Palomar/Principal/BusemannTails/Solution.lean'
  config['challenge_module']='Palomar.Principal.BusemannTails.Challenge'
  config['solution_module']='Palomar.Principal.BusemannTails.Solution'
  spec['proved_auxiliaries'].append('DirectedDistances.Example.record._proof_999')
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
if __name__=='__main__':unittest.main()
