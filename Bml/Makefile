default:
	make -C ../ bml

dependencies.svg: *.lean
	(echo "digraph {"; (grep -nr import *.lean | grep Bml | awk -F. '{print $$3 " -> " $$1}'); echo "}") | dot -Tsvg > dependencies.svg
