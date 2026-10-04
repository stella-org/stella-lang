module Test.Stella.CLI where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stella.CLI.Session as Session
import Test.Stella.CLI.Session.Attempter as Attempter
import Test.Stella.CLI.Session.Broker as Broker
import Test.Stella.CLI.Session.BrokerCodec as BrokerCodec
import Test.Stella.CLI.Session.Client as Client
import Test.Stella.CLI.Session.Value as SessionValue
import Test.Stella.CLI.Session.Parse as SessionParse

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Session.spec
  Client.spec
  SessionValue.spec
  SessionParse.spec
  BrokerCodec.spec
  Broker.spec
  Attempter.spec
