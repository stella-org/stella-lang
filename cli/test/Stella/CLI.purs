module Test.Stella.CLI where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stella.CLI.Session as Session
import Test.Stella.CLI.Session.Broker as Broker
import Test.Stella.CLI.Session.BrokerCodec as BrokerCodec
import Test.Stella.CLI.Session.Value as SessionValue

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Session.spec
  SessionValue.spec
  BrokerCodec.spec
  Broker.spec
