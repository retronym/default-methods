/*
 * Copyright (c) 2012, 2015, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

package defaultmethods

import java.lang.reflect.{Method, Modifier}

import scala.runtime.ObjectRef


// http://hg.openjdk.java.net/jdk9/jdk9/hotspot/file/fec31089c2ef/src/share/vm/classfile/defaultMethods.cpp

abstract class HierarchyVisitor {
  case class Node(var _class: Class[_], var _algorithm_data: Any, visit_super: Boolean) {
    var _super_was_visited: Boolean = !visit_super
    var interface_index: Int = 0

    def number_of_interfaces(): Int = { _class.getInterfaces.length; }
    def set_super_visited(): Unit = { _super_was_visited = true; }
    def increment_visited_interface(): Unit = { interface_index += 1; }
    def set_all_interfaces_visited(): Unit = {
      interface_index = number_of_interfaces()
    }
    def has_visited_super() = { _super_was_visited; }
    def has_visited_all_interfaces() = {
      interface_index >= number_of_interfaces()
    }
    def interface_at(index: Int) = {
      _class.getInterfaces()(index)
    }
    def next_super() = { _class.getSuperclass }
    def next_interface() = {
      interface_at(interface_index)
    }
  }

  var _cancelled: Boolean = false
  var _path = collection.mutable.ArrayBuffer[Node]()

  def current_top() = { _path.last; }
  def has_more_nodes() = _path.nonEmpty
  def push(cls: Class[_], data: Any) = {
    assert(cls != null, "Requires a valid instance class")
    val node = Node(cls, data, has_super(cls))
    _path += node
  }
  def pop() = { _path.remove(_path.size - 1); }

  def reset_iteration() {
    _cancelled = false
    _path.clear()
  }
  def is_cancelled() = { _cancelled; }

  // This code used to skip interface classes because their only
  // superclass was j.l.Object which would be also covered by class
  // superclass hierarchy walks. Now that the starting point can be
  // an interface, we must ensure we catch j.l.Object as the super.
  def has_super(cls: Class[_]) = {
    cls.getSuperclass != null
  }

  def node_at_depth(i: Int) = {
    if (i >= _path.length) null else _path.apply(_path.length - i - 1)
  }

  // Accessors available to the algorithm
  def current_depth() = { _path.length - 1; }

  def class_at_depth(i: Int): Class[_] = {
    val n = node_at_depth(i)
    if (n == null) null else n._class
  }
  def current_class() = { class_at_depth(0); }

  def data_at_depth(i: Int): Any = {
    val n = node_at_depth(i)
    if (n == null) null else n._algorithm_data
  }
  def current_data() = { data_at_depth(0); }

  def cancel_iteration() { _cancelled = true; }

  def new_node_data(cls: Class[_]): Any
  def free_node_data(data: Any): Unit = ()
  def visit(): Boolean

  def run(root: Class[_]) {
    reset_iteration()

    var algo_data = new_node_data(root)
    push(root, algo_data)
    var top_needs_visit = true

    do {
      toString
      var top: Node = current_top()

      if (top_needs_visit) {
        if (!visit()) {
          // algorithm does not want to continue along this path.  Arrange
          // it so that this state is immediately popped off the stack
          top.set_super_visited()
          top.set_all_interfaces_visited()
        }
        top_needs_visit = false
      }

      if (top.has_visited_super() && top.has_visited_all_interfaces()) {
        free_node_data(top._algorithm_data)
        pop()
      } else {
        var next: Class[_] = null
        if (!top.has_visited_super()) {
          next = top.next_super()
          top.set_super_visited()
        } else {
          next = top.next_interface()
          top.increment_visited_interface()
        }
        algo_data = new_node_data(next)
        push(next, algo_data)
        top_needs_visit = true
      }
    } while (!is_cancelled() && has_more_nodes())
  }
}

class PrintHierarchy extends HierarchyVisitor {
  def visit(): Boolean = {
    val cls = current_class()
    print("  " * current_depth())
    println(cls.getSimpleName)
    true
  }

  def new_node_data(cls: Class[_]): Any = { null; }
  override def free_node_data(data: Any): Unit = ()
}


// Iterates over the superinterface type hierarchy looking for all methods
// with a specific erased signature.
class FindMethodsByErasedSig(var _method_name: String, var _method_signature: String) extends HierarchyVisitor {
  var _family: StatefulMethodFamily = _

  class MethodFamily {
    val _members = collection.mutable.ArrayBuffer[(Method, ObjectRef[QualifiedState])]()
    val _member_index = collection.mutable.Map[Method, Int]()

    var _selected_target: Method = _
    // Filled in later, if a unique target exists
    var _exception_message: String = _
    // If no unique target is found
    var _exception_name: String = ""
    override def toString = s"MethodFamily(${_selected_target}, ${_exception_name}, ${_exception_message})"

    // If no unique target is found

    def contains_method(method: Method): Boolean = {
      _member_index.contains(method)
    }

    def add_method(method: Method, state: QualifiedState) = {
      println(s"${"  " * _path.length}${method.getDeclaringClass.getSimpleName}.${method.getName}=$state")
      _member_index(method) = _members.length
      _members += Tuple2(method, ObjectRef.create(state))
    }

    def disqualify_method(method: Method) = {
      println(s"${"  " * _path.length}${method.getDeclaringClass.getSimpleName}.${method.getName} = ${DISQUALIFIED}")
      _members.apply(_member_index(method))._2.elem = DISQUALIFIED
    }

    //  Symbol* generate_no_defaults_message(TRAPS) const;
    //  Symbol* generate_method_message(Symbol *klass_name, Method* method, TRAPS) const;
    //  Symbol* generate_conflicts_message(GrowableArray<Method*>* methods, TRAPS) const;

    def set_target_if_empty(m: Method) = {
      if (_selected_target == null /*&& !m.is_overpass()*/ ) {
        _selected_target = m
      }
    }

    def record_qualified_method(m: Method): Unit = {
      // If the method already exists in the set as qualified, this operation is
      // redundant.  If it already exists as disqualified, then we leave it as
      // disqualfied.  Thus we only add to the set if it's not already in the
      // set.
      if (!contains_method(m)) {
        add_method(m, QUALIFIED)
      }
    }

    def record_disqualified_method(m: Method) {
      // If not in the set, add it as disqualified.  If it's already in the set,
      // then set the state to disqualified no matter what the previous state was.
      if (!contains_method(m)) {
        add_method(m, DISQUALIFIED)
      } else {
        disqualify_method(m)
      }
    }

    def has_target() = {
      _selected_target != null
    }

    def throws_exception() = {
      _exception_message != null
    }

    def get_selected_target() = {
      _selected_target
    }

    def get_exception_message() = {
      _exception_message
    }

    def get_exception_name() = {
      _exception_name
    }

    // Either sets the target or the exception error message
    def determine_target(root: Class[_] /*, TRAPS*/) {
      if (has_target() || throws_exception()) {
        return
      }

      // Qualified methods are maximally-specific methods
      // These include public, instance concrete (=default) and abstract methods
      val qualified_methods = scala.collection.mutable.ArrayBuffer[Method]()
      var num_defaults = 0
      var default_index = -1
      var qualified_index = -1
      for (entry <- _members) {
        if (entry._2.elem == QUALIFIED) {
          qualified_methods.append(entry._1)
          qualified_index += 1
          if (entry._1.isDefault) {
            num_defaults += 1
            default_index = qualified_index
          }
        }
      }

      if (num_defaults == 0) {
        _exception_message = "none found"
        _exception_name = "AbstractMethodError"

        // If only one qualified method is default, select that
      } else if (num_defaults == 1) {
        _selected_target = qualified_methods.apply(default_index)

      } else if (num_defaults > 1) {
        _exception_message = qualified_methods.mkString("\n")
        _exception_name = "IncompatibleClassChangeError"
      }
    }

    def contains_signature(query: String) {
      _members.exists(m => descriptorOf(m._1) == query)
    }
  }

  sealed abstract class QualifiedState
  case object QUALIFIED extends QualifiedState
  case object DISQUALIFIED extends QualifiedState
  case class StatefulMethodFamily(var _qualification_state: QualifiedState = QUALIFIED, var _method_family: MethodFamily = new MethodFamily()) {

    def set_target_if_empty(m: Method) = _method_family.set_target_if_empty(m)

    def record_method_and_dq_further(m: Method): StateRestorer = {
      val mark = StateRestorer(_qualification_state, this)
      if (_qualification_state == QUALIFIED) {
        _method_family.record_qualified_method(m)
      } else {
        _method_family.record_disqualified_method(m)
      }
      // Everything found "above"??? this method in the hierarchy walk is set to
      // disqualified
      _qualification_state = DISQUALIFIED
      mark
    }

    def get_method_family(): MethodFamily = _method_family
  }
  case class StateRestorer(_state_to_restore: QualifiedState, _method: StatefulMethodFamily) {
    def restore_state() { _method._qualification_state = _state_to_restore; }
  }
  class PseudoScope {
    val marks = collection.mutable.ArrayBuffer[StateRestorer]()
    def add_mark(restorer: StateRestorer) = marks += restorer

    def destroy(): Unit = marks.foreach(_.restore_state())
    override def toString = "<>"
  }

  def get_discovered_family: MethodFamily = {
      if (_family != null) {
        _family.get_method_family()
      } else {
        null
      }
  }

  def new_node_data(cls: Class[_]) = { new PseudoScope(); }
  override def free_node_data(node_data: Any): Unit = {
    node_data.asInstanceOf[PseudoScope].destroy()
  }

  def descriptorOf(m: Method): String = {
    java.lang.invoke.MethodType.methodType(m.getReturnType, m.getParameterTypes).toMethodDescriptorString
  }

  // Find all methods on this hierarchy that match this
  // method's erased (name, signature)
  def visit(): Boolean = {
    println(s"${"  " * _path.length}${_path.last._class.getSimpleName}")
    val scope = current_data().asInstanceOf[PseudoScope]
    val iklass = current_class()

    val m = iklass.getDeclaredMethods.find(x => x.getName == _method_name && descriptorOf(x) == _method_signature).orNull
    // private interface methods are not candidates for default methods
    // invokespecial to private interface methods doesn't use default method logic
    // private class methods are not candidates for default methods,
    // private methods do not override default methods, so need to perform
    // default method inheritance without including private methods
    // The overpasses are your supertypes' errors, we do not include them
    // future: take access controls into account for superclass methods
    if (m != null && !Modifier.isStatic(m.getModifiers) && /*!m->is_overpass() && */ !Modifier.isPrivate(m.getModifiers)) {
      if (_family == null) {
        _family = StatefulMethodFamily()
      }

      if (iklass.isInterface) {
        val restorer: StateRestorer = _family.record_method_and_dq_further(m)
        scope.add_mark(restorer)
      } else {
        // This is the rule that methods in classes "win" (bad word) over
        // methods in interfaces. This works because of single inheritance
        // private methods in classes do not "win", they will be found
        // first on searching, but overriding for invokevirtual needs
        // to find default method candidates for the same signature
        _family.set_target_if_empty(m)
      }
    }
    true
  }
}


object Defaults {
  def main(args: Array[String]): Unit = {
    def test(klass: Class[_], name: String, sig: String): Unit = {
      val findMethodsByErasedSig = new FindMethodsByErasedSig(name, sig)
      findMethodsByErasedSig.run(klass)
      val methodFamily = findMethodsByErasedSig.get_discovered_family
      if (methodFamily != null) {
        methodFamily.determine_target(klass)
        println(methodFamily)
        Console.out.flush()
        assert(methodFamily._exception_name == "")
      }
    }
    test(classOf[java.util.AbstractSet[_]], "spliterator", "()Ljava/util/Spliterator;")
    test(classOf[List[_]], "head", "()Ljava/lang/Object;")
  }
}
