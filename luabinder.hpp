// //////////////////////////////////////////////////////////////////////////
// Small but powerful Lua 5.1 / C++ binder, uses boost.MPL, function, fusion, bind, function_types, in_place_factory & type_traits
// The whole file content is written by Belskiy Pavel, 2009
// If you want to use the following code or any part of it in your programms, you MUST put THIS comment in your code as well.
// (c) Belskiy Pavel, 2009
// //////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////
// TODO:
// 1. DONE - Accept const references in pushToStack() functions. Save info about constness.
// 1a. DONE - const char* as a special case.
// 2. DONE - define various ownership policies
// 3. Register constructors, perhaps via (typed)inPlaceFactory
// 4. DONE - Manage lua metatables, allow to register member functions.
// 5. Add ability to call Lua functions from C++
// 6. Добавить создание/просмотр/слежение за комплексными таблицами/переменными Lua из C++
// 7. ... functors introspection...
//////////////////////////////////////////////////////////////////////////
#include <boost/mpl/vector.hpp>
#include <boost/mpl/int.hpp>
#include <boost/mpl/begin_end.hpp>
#include <boost/mpl/next.hpp>
#include <boost/mpl/deref.hpp>
#include <boost/mpl/find.hpp>
#include <boost/mpl/logical.hpp>
#include <boost/mpl/distance.hpp>
#include <boost/mpl/pop_front.hpp>
#include <boost/mpl/front.hpp>
#include <boost/mpl/equal.hpp>
#include <boost/mpl/contains.hpp>
#include <boost/noncopyable.hpp>
#include <boost/function.hpp>
#include <boost/fusion/include/cons.hpp>
#include <boost/fusion/include/push_back.hpp>
#include <boost/fusion/include/invoke.hpp>
#include <boost/bind.hpp>
#include <boost/function_types/parameter_types.hpp>
#include <boost/function_types/function_pointer.hpp>
#include <boost/utility/enable_if.hpp>
#include <boost/type_traits.hpp>
#include <boost/shared_ptr.hpp>
#include <lua.hpp>
#include <string>
#include <cstring>
#include <map>
#include <vector>
#include <typeinfo>

namespace mpl = boost::mpl;

template<class T>
struct remove_cv_ref: boost::remove_cv< typename boost::remove_reference<T>::type > {};

template<class T>
struct remove_pointers
{
private:
  typedef typename boost::remove_pointer<T>::type rem;
public:
	typedef typename mpl::eval_if<boost::is_pointer<rem>,
		remove_pointers<rem>,
		mpl::identity<rem> >::type type;
};

struct LuaException
{
	std::string what;

	LuaException(const std::string & w) : what(w) {}
};

struct LuaSyntaxError : LuaException
{
	LuaSyntaxError(const std::string & w) : LuaException(w) {}
};

struct LuaRuntimeError : LuaException
{
	LuaRuntimeError(const std::string & w) : LuaException(w) {}
};

struct LuaConvertError : LuaException
{
	LuaConvertError(int argn, const std::string & ttype): LuaException("")
	{
		std::stringstream t;
		t << "Cannot convert argument " << argn << " to " << ttype << " type";
		what = t.str();
	}
};

template <class T> struct Type2Type
{
	typedef T type;
};

// Классы политик хранения
// 1. Простая политика - сохранение указателя на объект, не управление временем жизни

struct SimplePointerPolicy
{
	template <class T>
	struct apply
	{
		static inline void* getTypeHolder(const T * holdee)
		{
			return (void*) (const_cast<T*> (holdee));
		}
		static inline void* getTypeHolder(T * holdee)
		{
			return (void*) holdee;
		}
		static inline T * getHoldee(void* holder)
		{
			return reinterpret_cast<T*> (holder);
		}
		static inline const T * getConstHoldee(void* holder)
		{
			return reinterpret_cast<T*> (holder);
		}
		static inline void onMetaGc(void*)
		{
			// Do nothing;
		}
	};
};

// 2. Сохранение указателя на объект, объект удаляется при дергании __gc Lua

struct GcPointerPolicy
{
	template <class T>
	struct apply : SimplePointerPolicy::apply<T>
	{
		static inline void onMetaGc(void* holder)
		{
			const T* holdee = SimplePointerPolicy::apply<T>::getConstHoldee(holder);
			delete holdee;
		}
	};
};

struct StdPointerPolicy { template<class T> struct apply {};};

namespace TypeManagerDetail
{
	struct SimpleDelPolicy
	{
		template <class T>
		static inline int apply(lua_State * state)
		{
			T* udata = reinterpret_cast<T*> (lua_touserdata(state, -1));
			udata->~T();
			return 0;
		}
	};

	template <class T>
	void* allocateLuaSpace(lua_State *state, const char *tname, bool saveit = true)
	{
		static unsigned int curindex = 1;
		void *result = lua_newuserdata(state, sizeof (T)); // Lua Stack +1 udata
		if (luaL_newmetatable(state, tname)) // Lua Stack +2 udata meta
		{
			lua_pushstring(state, "__gc"); //Lua Stack +3 udata meta "__gc"
			lua_pushcfunction(state, & SimpleDelPolicy::apply<T>); // Lua Stack +4 udata meta "__gc" func
			lua_rawset(state, -3); // Lua Stack +2 udata meta

			//lua_pushstring(state, "__index"); //Lua Stack +3 udata meta "__index"
			//lua_pushvalue(state, -2); //Lua Stack +4 udata meta "__index" meta
			//lua_rawset(state, -3); // Lua Stack +2 udata meta
		}
		lua_setmetatable(state, -2); // Lua Stack +1 udata
		if (saveit)
		{
			//Ensure that the object will not be deleted by saving its reference into a table in the registry
			lua_getfield(state, LUA_REGISTRYINDEX, "LUABINDER_Alloc"); // Lua Stack +2 udata table
			if (!lua_istable(state, -1))
			{
				// The table is not created yet
				lua_pushstring(state, "LUABINDER_Alloc"); // Lua Stack +3 udata nil "LUABINDER.."
				lua_newtable(state); // Lua Stack +4 udata nil "LUABINDER.." table
				lua_rawset(state, LUA_REGISTRYINDEX); // Lua Stack +2 udata nil
				lua_pop(state, 1); // Lua Stack +1 udata
				lua_getfield(state, LUA_REGISTRYINDEX, "LUABINDER_Alloc"); // Lua Stack +2 udata table
			}
			lua_pushvalue(state, -2); // Lua Stack +3 udata table udata
			lua_rawseti(state, -2, curindex); // Lua Stack +2 udata table
			lua_pop(state, 2); // Lua Stack 0
			curindex++;
		}
		// Lua Stack +1 udata
		return result;
	}

	template<class T> const std::type_info& templatedTypeid()
	{
		return typeid(T);
	}

	struct StackImplBase
	{
		struct MetaData
		{
			std::string name;
			const std::type_info& (*staticInfoGetter) ();

			bool operator ==(const MetaData & r)const
			{
				return name == r.name;
			}
			bool operator !=(const MetaData & r) const
			{
				return !operator ==(r);
			}
		};

		template <class T>
		struct DataHolder
		{
			const MetaData* meta;
			bool isConst;
			bool copyOnConstRem;
			void* data;
			T * (*getData)(void*);
			const T * (*getConstData)(void*);
			void (*onGC)(void*);

			~DataHolder() {
				onGC(data);
			}
		};

		// Указатели MetaData* указывают на область памяти, выделенной Lua.
		// Эти области являются full userdata и удаляются вместе с закрытием контекста Lua
		// по метасобытию __gc
		boost::shared_ptr<std::vector<MetaData*> > mdata;

		StackImplBase() : mdata(new std::vector<MetaData*>()) {}

		StackImplBase(const boost::shared_ptr<std::vector<MetaData*> >& data) : mdata(data) {}

		void _igetFromStack();
		void _ipushToStack();
	};
	template <class TList, int _Idx> struct StackImpl;

	template <int _Idx> struct StackImpl<mpl::vector<>, _Idx> : StackImplBase
	{
		StackImpl(const boost::shared_ptr<std::vector<StackImplBase::MetaData*> >& data) :StackImplBase(data) {}

		StackImpl() {}
		void _igetFromStack(int);
		void _ipushToStack(int);
	};

	template <class TList, int _Idx> struct genInherit
	{
	private:
		typedef typename mpl::pop_front<TList>::type tOne;
	public:
		typedef typename mpl::if_<
			typename mpl::equal<tOne, mpl::vector<> >::type,
			StackImplBase,
			StackImpl<tOne, _Idx + 1 > >::type type;
	};

	template <class TList, int _Idx> struct StackImpl : genInherit<TList, _Idx>::type
	{
	private:
		typedef typename mpl::front<TList>::type CurrType;
	public:
		StackImpl(const boost::shared_ptr<std::vector<StackImplBase::MetaData*> >& data)
			:genInherit<TList, _Idx>::type(data) {}

		StackImpl() {}

		inline CurrType * _igetFromStack(lua_State* L, int ind, Type2Type<CurrType*>) const
		{
			if (lua_isuserdata(L, ind))
			{
				StackImplBase::DataHolder<CurrType>* myDataHolder = reinterpret_cast<StackImplBase::DataHolder<CurrType>*> (lua_touserdata(L, ind));
				if ((*myDataHolder->meta) != (*this->StackImplBase::mdata->at(_Idx)))
					throw LuaConvertError(ind, this->StackImplBase::mdata->at(_Idx)->name);
				if (myDataHolder->isConst)
				{
					if (myDataHolder->copyOnConstRem)
					{
						//const CurrType* obj = myDataHolder->getConstData(myDataHolder->data);
						//CurrType *itsCopy = new (allocateLuaSpace<CurrType > (L, "temporary")) CurrType(*obj);
						//return itsCopy;
					} else
						throw LuaConvertError(ind, this->StackImplBase::mdata->at(_Idx)->name);
				}
				return myDataHolder->getData(myDataHolder->data);
			}
			throw LuaConvertError(ind, this->StackImplBase::mdata->at(_Idx)->name);
		}

		inline const CurrType * _igetFromStack(lua_State* L, int ind, Type2Type<const CurrType*>) const
		{
			if (lua_isuserdata(L, ind))
			{
				StackImplBase::DataHolder<CurrType>* myDataHolder = reinterpret_cast<StackImplBase::DataHolder<CurrType>*> (lua_touserdata(L, ind));
				if ((*myDataHolder->meta) != (*this->StackImplBase::mdata->at(_Idx)))
					throw LuaConvertError(ind, std::string("const ") + this->StackImplBase::mdata->at(_Idx)->name);
				return myDataHolder->getConstData(myDataHolder->data);
			}
			throw LuaConvertError(ind, std::string("const ") + this->StackImplBase::mdata->at(_Idx)->name);
		}

		template <class SavePolicy>
		inline void _ipushToStack(lua_State* L, CurrType* topush, Type2Type<CurrType*>) const
		{
			typedef typename mpl::if_<boost::is_same<SavePolicy, StdPointerPolicy>,
				SimplePointerPolicy::apply<CurrType>,
				typename SavePolicy::template apply<CurrType> >::type realSavePolicy;
			StackImplBase::MetaData* myMeta = this->StackImplBase::mdata->at(_Idx);
			StackImplBase::DataHolder<CurrType>* myDataHolder =
				new(allocateLuaSpace<StackImplBase::DataHolder<CurrType> >(L, myMeta->name.c_str(), false)) StackImplBase::DataHolder<CurrType>;
			myDataHolder->meta = myMeta;
			myDataHolder->data = realSavePolicy::getTypeHolder(topush);
			myDataHolder->isConst = false;
			myDataHolder->copyOnConstRem = false;
			myDataHolder->getConstData = &realSavePolicy::getConstHoldee;
			myDataHolder->getData = &realSavePolicy::getHoldee;
			myDataHolder->onGC = &realSavePolicy::onMetaGc;
		}

		template <class SavePolicy>
		inline void _ipushToStack(lua_State* L, const CurrType& topush, Type2Type<const CurrType>) const
		{
			typedef typename mpl::if_<boost::is_same<SavePolicy, StdPointerPolicy>,
				GcPointerPolicy::apply<CurrType>,
				typename SavePolicy::template apply<CurrType> >::type realSavePolicy;
			StackImplBase::MetaData *myMeta = this->StackImplBase::mdata->at(_Idx);
			StackImplBase::DataHolder<CurrType>* myDataHolder =
				new(allocateLuaSpace<StackImplBase::DataHolder<CurrType> >(L, myMeta->name.c_str(), false)) StackImplBase::DataHolder<CurrType>;
			myDataHolder->meta = myMeta;
			myDataHolder->data = realSavePolicy::getTypeHolder(new CurrType(topush));
			myDataHolder->isConst = false;
			myDataHolder->copyOnConstRem = false;
			myDataHolder->getConstData = &realSavePolicy::getConstHoldee;
			myDataHolder->getData = &realSavePolicy::getHoldee;
			myDataHolder->onGC = &realSavePolicy::onMetaGc;
		}

		template <class SavePolicy>
		inline void _ipushToStack(lua_State* L, const CurrType* topush, Type2Type<const CurrType*>) const
		{
			typedef typename mpl::if_<boost::is_same<SavePolicy, StdPointerPolicy>,
				GcPointerPolicy::apply<CurrType>,
				typename SavePolicy::template apply<CurrType> >::type realSavePolicy;
			StackImplBase::MetaData *myMeta = this->StackImplBase::mdata->at(_Idx);
			StackImplBase::DataHolder<CurrType>* myDataHolder =
				new(allocateLuaSpace<StackImplBase::DataHolder<CurrType> >(L, myMeta->name.c_str(), false)) StackImplBase::DataHolder<CurrType>;
			myDataHolder->meta = myMeta;
			myDataHolder->data = realSavePolicy::getTypeHolder(topush);
			myDataHolder->isConst = true;
			myDataHolder->copyOnConstRem = false;
			myDataHolder->getConstData = &realSavePolicy::getConstHoldee;
			myDataHolder->getData = &realSavePolicy::getHoldee;
			myDataHolder->onGC = &realSavePolicy::onMetaGc;
		}
		using genInherit<TList, _Idx>::type::_igetFromStack;
		using genInherit<TList, _Idx>::type::_ipushToStack;
	};

#	define CREATOR_FUNC_ARITY 8
#	define CREATOR_FUNC_PARAM_ITEM(z, n, unused) typename boost::fusion::result_of::at_c<FusedArgs, n>::type Arg##n
#	define CREATOR_FUNC_ITEM(z, n, unused) template <class T, class FusedArgs> \
	T* creatorFunc(BOOST_PP_ENUM(n, CREATOR_FUNC_PARAM_ITEM, unused) BOOST_PP_COMMA_IF(n) void* place) \
	{ \
		return new(place) T(BOOST_PP_ENUM_PARAMS(n, Arg)); \
	};

	BOOST_PP_REPEAT(CREATOR_FUNC_ARITY, CREATOR_FUNC_ITEM, ~)
#	undef CREATOR_FUNC_ITEM
#	undef CREATOR_FUNC_PARAM_ITEM
#	undef CREATOR_FUNC_ARITY

	/*template <class T, class FusedArgs>
	T* genericCreator(const FusedArgs& arg, void* place)
	{
		typedef typename boost::fusion::result_of::push_back<FusedArgs, void*>::type realArgsType;
		typedef typename boost::fusion::result_of::push_front<realArgsType, T*>::type funcArgsType;
		typedef typename boost::function_types::function_pointer<funcArgsType>::type funcType;

		return boost::fusion::invoke((funcType) & creatorFunc, boost::fusion::push_back(arg, place));
	}*/
}

// Тип возврата функций getFromStack
// Скаляры возвращаются собой, объекты через указатели

template <class T> struct getTraits :
mpl::eval_if<boost::is_scalar<T>,
mpl::identity<T>,
mpl::if_<boost::is_same<std::string, typename boost::remove_pointer<typename remove_cv_ref<T>::type>::type>,
T,
boost::reference_wrapper<T>
>
> {};

template <class TypesList>
class LuaTypesManager : protected TypeManagerDetail::StackImpl<TypesList, 0 >, public boost::noncopyable
{
public:
	template < class T > struct AddedType
	{
		typedef LuaTypesManager<typename mpl::push_back<TypesList, T>::type> type;
	};

	template <class T, int Dummy = 0> struct isRegistred : mpl::contains<TypesList, T> {};
	template <int Dummy> struct isRegistred<int, Dummy> : mpl::true_ {};
	template <int Dummy> struct isRegistred<std::string, Dummy> : mpl::true_ {};
	template <int Dummy> struct isRegistred<const char*, Dummy> : mpl::true_ {};
	template <int Dummy> struct isRegistred<float, Dummy> : mpl::true_ {};

	template <class T, int Dummy = 0> struct purify : boost::remove_cv<typename boost::remove_pointer<typename remove_cv_ref<T>::type>::type> {};
	template <int Dummy> struct purify<const char*, Dummy> : mpl::identity<const char*> {};

	LuaTypesManager() {}

	LuaTypesManager(const boost::shared_ptr<std::vector<TypeManagerDetail::StackImplBase::MetaData*> >& data) :
	TypeManagerDetail::StackImpl<TypesList, 0 > (data) {}
	typedef TypesList tlist;
	typedef LuaTypesManager<TypesList> type;
	typedef boost::shared_ptr<LuaTypesManager<tlist> > pointer;

	template <class T> inline typename AddedType<T>::type::pointer
		registerType(const std::string& name, lua_State* state)
	{
		TypeManagerDetail::StackImplBase::MetaData* temp =
			new (TypeManagerDetail::allocateLuaSpace<TypeManagerDetail::StackImplBase::MetaData > (state, "LUABINDMetaData"))
			TypeManagerDetail::StackImplBase::MetaData;
		temp->name = name;
		temp->staticInfoGetter = & TypeManagerDetail::templatedTypeid<T> ;
		this->TypeManagerDetail::StackImplBase::mdata->push_back(temp);
		boost::shared_ptr<std::vector<TypeManagerDetail::StackImplBase::MetaData*> > myvec = this->TypeManagerDetail::StackImplBase::mdata;
		this->TypeManagerDetail::StackImplBase::mdata.reset();
		// Устанавливаем метатаблицу, если ее нет
		if (luaL_newmetatable(state, name.c_str())) // Lua Stack +1 meta
		{
			lua_pushstring(state, "__gc"); //Lua Stack +2 meta "__gc"
			lua_pushcfunction(state, & TypeManagerDetail::SimpleDelPolicy::apply<TypeManagerDetail::StackImplBase::DataHolder<T> >); // Lua Stack +3 meta "__gc" func
			lua_rawset(state, -3); // Lua Stack +1 meta

			lua_pushstring(state, "__index"); //Lua Stack +2 meta "__index"
			lua_pushvalue(state, -2); //Lua Stack +3 meta "__index" meta
			lua_rawset(state, -3); // Lua Stack +1 meta
		}
		lua_pop(state, 1);

		return typename AddedType<T>::type::pointer
			(new typename AddedType<T>::type(myvec));
	}
protected:

	inline int _igetFromStack(lua_State* L, int ind, Type2Type<int>) const
	{
		if (lua_isnumber(L, ind))
			return lua_tointeger(L, ind);
		throw LuaConvertError(ind, "int");
	}
	inline std::string _igetFromStack(lua_State* L, int ind, Type2Type<std::string>) const
	{
		if (lua_isstring(L, ind))
			return std::string(lua_tostring(L, ind));
		throw LuaConvertError(ind, "std::string");
	}
	inline const char* _igetFromStack(lua_State* L, int ind, Type2Type<const char*>) const
	{
		if (lua_isstring(L, ind))
			return lua_tostring(L, ind);
		throw LuaConvertError(ind, "const char*");
	}
	inline float _igetFromStack(lua_State* L, int ind, Type2Type<float>) const
	{
		if (lua_isnumber(L, ind))
			return lua_tonumber(L, ind);
		throw LuaConvertError(ind, "float");
	}

	template <class SavePolicy>
	inline void _ipushToStack(lua_State* L, int number, Type2Type<int>) const
	{
		lua_pushinteger(L, number);
	}
	template <class SavePolicy>
	inline void _ipushToStack(lua_State* L, const char* str, Type2Type<const char*>) const
	{
		lua_pushstring(L, str);
	}
	template <class SavePolicy>
	inline void _ipushToStack(lua_State* L, const std::string& str, Type2Type<std::string>) const
	{
		lua_pushstring(L, str.c_str());
	}
	template <class SavePolicy>
	inline void _ipushToStack(lua_State* L, float num, Type2Type<float>) const
	{
		lua_pushnumber(L, num);
	}
	using TypeManagerDetail::StackImpl<TypesList, 0 > ::_igetFromStack;
	using TypeManagerDetail::StackImpl<TypesList, 0 > ::_ipushToStack;

	template <class T> struct _dereference
	{
		static inline T & apply(T * _o) {return *_o;}
		typedef Type2Type<T> type;
	};
	template <class T> struct _identity
	{
		static inline T * apply(T * _o) {return _o;}
		typedef Type2Type<T*> type;
	};

	template <class T> struct _getIdentity
	{
		static inline T & apply(T& _o, lua_State*) {return _o;}
		static inline T & apply(T* _o, lua_State*) {return *_o;}
		typedef typename mpl::if_<boost::is_pointer<T>,
			Type2Type<T>, Type2Type<T*> >::type type;
	};
	template <class T, int Dummy = 0> struct _getScalar
	{
		static inline T apply(T _o, lua_State*) {return _o;}
		typedef Type2Type<typename boost::remove_cv<T>::type > type;
	};
	template <class T, int Dummy> struct _getScalar<T*, Dummy>
	{
		static inline T * apply(T _o, lua_State * L)
		{
			T* temp = new (TypeManagerDetail::allocateLuaSpace<T > (L, typeid (T).name(), false)) T(_o);
			lua_pop(L, 1);
			return temp;
		}
		typedef Type2Type<typename boost::remove_cv<T>::type > type;
	};

	template <int Dummy> struct _getScalar<const char*, Dummy>
	{
		static inline const char* apply(const char* _o, lua_State * L) {return _o;}
		typedef Type2Type<const char*> type;
	};
public:

	template <class T>
	inline typename getTraits<T>::type getFromStack(lua_State* L, int idx)const
	{
		typedef typename mpl::if_ < mpl::contains<TypesList, typename boost::remove_cv<typename boost::remove_pointer<T>::type>::type>,
			_getIdentity<T>,
			_getScalar<T> >::type decisiveType;
		return typename getTraits<T>::type(decisiveType::apply(_igetFromStack(L, idx, typename decisiveType::type()), L));
	}

	template <class SavePolicy, class T>
	inline void pushToStack(lua_State* L, T* obj, SavePolicy) const
	{
		typedef typename mpl::if_<mpl::contains<TypesList, T>,
			_identity<T>, _dereference<T> >::type decisiveType;
		_ipushToStack<SavePolicy > (L, decisiveType::apply(obj), decisiveType::type());
	}

	template <class SavePolicy, class T>
	inline void pushToStack(lua_State* L, const T* obj, SavePolicy) const
	{
		typedef typename mpl::if_<mpl::contains<TypesList, T>,
			_identity<const T>, _dereference<const T> >::type decisiveType;
		_ipushToStack<SavePolicy > (L, decisiveType::apply(obj), decisiveType::type());
	}

	template <class SavePolicy, class T>
	inline void pushToStack(lua_State* L, T& obj, SavePolicy) const
	{
		//std::cout << "Unconst push to stack" << std::endl;
		//_ipushToStack(L, obj, Type2Type<T > ());
		pushToStack(L, &obj, SavePolicy());
	}

	template <class SavePolicy, class T>
	inline void pushToStack(lua_State* L, const T& obj, SavePolicy) const
	{
		// Если тип зарегистрирован, но не находится в TypesList,
		// то передаем уже имеющимся функциям
		//std::cout << "Const push to stack" << std::endl;
		typedef typename mpl::if_<mpl::contains<TypesList, T>,
			Type2Type<const T>,
			Type2Type<T> >::type decisiveType;
		_ipushToStack<SavePolicy > (L, obj, decisiveType());
	}

	template <class T>
	inline void pushToStack(lua_State* L, T* obj) const
	{
		pushToStack(L, obj, StdPointerPolicy());
	}

	template <class T>
	inline void pushToStack(lua_State* L, const T* obj) const
	{
		pushToStack(L, obj, StdPointerPolicy());
	}

	template <class T>
	inline void pushToStack(lua_State* L, T& obj) const
	{
		pushToStack(L, obj, StdPointerPolicy());
	}

	template <class T>
	inline void pushToStack(lua_State* L, const T& obj) const
	{
		pushToStack(L, obj, StdPointerPolicy());
	}
};

typedef LuaTypesManager<mpl::vector<> > LTypesManager;

class LuaFuncCaller
{
public:
	template <class SavePolicy, typename Func,
	class From = typename mpl::begin<typename boost::function_types::parameter_types<Func>::type>::type,
	class End = typename mpl::end<typename boost::function_types::parameter_types<Func>::type>::type>
	struct invoker;

	typedef boost::function<int () > FunctionInvokerType;

	template <class SavePolicy, typename Func, class ConvertTList>
	LuaFuncCaller(lua_State* L, Func f, const boost::shared_ptr<LuaTypesManager<ConvertTList> >&, SavePolicy);

	LuaFuncCaller() {}

	int operator() ()
	{
		return funcHolder();
	}
private:
	FunctionInvokerType funcHolder;
};

template <class SavePolicy, typename Func, class From, class End>
struct LuaFuncCaller::invoker
{
	typedef typename boost::mpl::deref<From>::type argType;
	typedef typename boost::mpl::next<From>::type nextIter;
	typedef typename boost::remove_reference<argType>::type clearedArgT;

	template <class StackIdx, class FusedArgs, class ConvertTList>
	static inline int apply(Func f, lua_State* eng, FusedArgs argCons, const boost::shared_ptr<LuaTypesManager<ConvertTList> >& convertor)
	{
		return LuaFuncCaller::invoker<SavePolicy, Func, nextIter, End>::template apply<typename StackIdx::next > (f, eng, boost::fusion::push_back(argCons, convertor->template getFromStack<clearedArgT > (eng, StackIdx::value)), convertor);
	}
};

template <class SavePolicy, typename Func, class End>
struct LuaFuncCaller::invoker<SavePolicy, Func, End, End>
{
	struct invokeConvertPolicy
	{
		template <class FusedArgs, class ConvertTList>
		static inline int apply(Func f, lua_State* st, FusedArgs argCons, const boost::shared_ptr<LuaTypesManager<ConvertTList> >& conv)
		{
			conv->pushToStack(st, boost::fusion::invoke(f, argCons), SavePolicy());
			return 1;
		}
	};
	struct invokeOnlyPolicy
	{
		template <class FusedArgs, class ConvertTList>
		static inline int apply(Func f, lua_State*, FusedArgs argCons, const boost::shared_ptr<LuaTypesManager<ConvertTList> >&)
		{
			boost::fusion::invoke(f, argCons);
			return 0;
		}
	};

	template <class StackIdx, class FusedArgs, class ConvertTList>
	static inline int apply(Func f, lua_State* st, FusedArgs argCons, const boost::shared_ptr<LuaTypesManager<ConvertTList> >& conv)
	{
		typedef typename boost::fusion::result_of::invoke<Func, FusedArgs>::type resType;
		typedef LuaTypesManager<ConvertTList> myTypeManager;
		typedef typename myTypeManager::template purify<resType>::type purifiedType;
		typedef typename mpl::if_<typename myTypeManager::template isRegistred<purifiedType>::type,
			invokeConvertPolicy,
			invokeOnlyPolicy >::type myPolicy;
		return myPolicy::apply(f, st, argCons, conv);
	}
};

template <class SavePolicy, typename Func, class ConvertTList>
LuaFuncCaller::LuaFuncCaller(lua_State* L, Func f, const boost::shared_ptr<LuaTypesManager<ConvertTList> >& convertor, SavePolicy)
{
	funcHolder = boost::bind(& invoker<SavePolicy, Func>::template apply<mpl::int_ < 1 >, boost::fusion::nil, ConvertTList>, f, L, boost::fusion::nil(), convertor);
}

template <class Convertor = LTypesManager>
class LuaEngine
{
public:
	LuaEngine(lua_State* state)
	{
		m_conv = typename Convertor::pointer(new Convertor);
		m_state = state;
	}
	LuaEngine(lua_State* state, const typename Convertor::pointer& p) :m_conv(p), m_state(state) {}

	~LuaEngine() {}

	template <class SavePolicy, class Func>
	inline LuaEngine<Convertor>& regFunc(const char* name, Func f, SavePolicy)
	{
		//funcsToCall.insert(std::make_pair(name, LuaFuncCaller(m_state, f, *m_conv)));
		new(TypeManagerDetail::allocateLuaSpace<LuaFuncCaller > (m_state, "LuaFuncCaller", false))
			LuaFuncCaller(m_state, f, m_conv, SavePolicy());
		//lua_pushlightuserdata(m_state, &(funcsToCall[name]));
		lua_pushcclosure(m_state, & LuaEngine<Convertor>::cfuncCaller, 1);
		lua_setfield(m_state, LUA_GLOBALSINDEX, name);
		return *this;
	}

	template <class SavePolicy, class Func>
	inline LuaEngine<Convertor>& regMeta(const char* typeName, const char* metaName, Func f, SavePolicy)
	{
		if (std::strcmp(metaName, "__gc") == 0 || std::strcmp(metaName, "__index") == 0)
			return *this;
		// Таблица уже должна быть создана, выходим если не так
		lua_pushstring(m_state, typeName);
		lua_rawget(m_state, LUA_REGISTRYINDEX);
		if (lua_istable(m_state, -1))
		{
			lua_pushstring(m_state, metaName);
			new (TypeManagerDetail::allocateLuaSpace<LuaFuncCaller > (m_state, "LuaFuncCaller", false))
				LuaFuncCaller(m_state, f, m_conv, SavePolicy());
			lua_pushcclosure(m_state, & LuaEngine<Convertor>::cfuncCaller, 1);
			lua_rawset(m_state, -3);
		}
		lua_pop(m_state, 1);
		return *this;
	}

	template <class Func>
	inline LuaEngine<Convertor>& regFunc(const char* name, Func f)
	{
		return regFunc(name, f, StdPointerPolicy());
	}

	template <class Func>
	inline LuaEngine<Convertor>& regMeta(const char* typeName, const char* metaName, Func f)
	{
		return regMeta(typeName, metaName, f, StdPointerPolicy());
	}

	template <class T>
	inline LuaEngine<typename Convertor::template AddedType<T>::type>
		regType(const std::string& name)
	{
		return LuaEngine<typename Convertor::template AddedType<T>::type > (m_state, m_conv->template registerType<T> (name, m_state));
	}

	template <class T>
	inline LuaEngine<Convertor>& regVar(const char* name, T& var)
	{
		m_conv->pushToStack(m_state, var);
		lua_setglobal(m_state, name);
		return *this;
	}
private:
	typename Convertor::pointer m_conv;
	lua_State* m_state;

	static int cfuncCaller(lua_State* L)
	{
		LuaFuncCaller* funcCaller = reinterpret_cast<LuaFuncCaller*> (lua_touserdata(L, lua_upvalueindex(1)));
		try
		{
			return (*funcCaller)();
		} 
		catch (LuaException& e)
		{
			luaL_error(L, "%s", e.what.c_str());
		}
		return 0;
	}
};

inline void execLuaString(lua_State *m_state, const char *str)
{
	if (luaL_loadstring(m_state, str) != 0)
	{
		LuaSyntaxError err(lua_tostring(m_state, -1));
		lua_pop(m_state, 1);
		throw err;
	}
	if (lua_pcall(m_state, 0, LUA_MULTRET, 0) != 0)
	{
		LuaRuntimeError err(lua_tostring(m_state, -1));
		lua_pop(m_state, 1);
		throw err;
	}
}
