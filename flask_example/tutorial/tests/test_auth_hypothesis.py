from flaskr import create_app
from flaskr.db import init_db

import tempfile
import os

import hypothesis.strategies as st
from hypothesis import assume
from hypothesis.stateful import RuleBasedStateMachine, rule, precondition

class StatefulFlaskrTest(RuleBasedStateMachine):
    def __init__(self):
        super().__init__()

        # start application
        self.db_fd, self.db_path = tempfile.mkstemp()
        self.app = create_app({"TESTING": True, "DATABASE": self.db_path})
        with self.app.app_context():
            init_db()
        self.client = self.app.test_client()

        # set up model
        self.registered = {}
        self.logged_in = None


    def teardown(self):
        # clean up application
        os.close(self.db_fd)
        os.unlink(self.db_path)

    def registered_users(self, draw):
        assume(self.registered)
        return list(self.registered.items())[draw(st.integers()) % len(self.registered)]

    @rule(data=st.data())
    def log_in(self, data):
        username, password = self.registered_users(data.draw)

        response = self.client.post(
            "/auth/login", data={"username": username, "password": password}
        )

        assert response.status_code == 302
        assert response.headers["Location"] == "/"

        self.logged_in = username

    @precondition(lambda self: self.logged_in is None)
    @rule()
    def log_out(self):
        response = self.client.get("/auth/logout")

        assert response.status_code == 302
        assert response.headers["Location"] == "/"

        self.logged_in = None


    @precondition(lambda self: self.logged_in is None)
    @rule(username=st.text(min_size=1), password=st.text(min_size=1))
    def register(self, username, password):
        assume(username not in self.registered)

        response = self.client.post(
            "/auth/register", data={"username": username, "password": password}
        )

        assert response.status_code == 302
        assert response.headers["Location"] == "/auth/login"

        self.registered[username] = password

    @rule()
    def create(self):
        response = self.client.post("/create", data={"title": "", "body": ""})

        if self.logged_in is None:
            assert response.status_code == 302
            assert response.headers["Location"] == "/auth/login"
        else:
            response.status_code == 200

    
    @rule()
    def view(self):
        self.client.get("/")

TestFlaskr = StatefulFlaskrTest.TestCase
